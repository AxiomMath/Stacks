module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsorIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsor of trivializations of the unit pair is the Kummer torsor

Let `C` be a site and `F : C ⥤ Scheme` a functor whose global functions form a sheaf of
commutative rings, so that `(C, F.op ⋙ Γ)` is a ringed site, let `T` be a terminal object of
`C`, and let `a` be a unit of the global functions on `F T`. The *unit pair* at `a` is the
structure sheaf `O`, which is invertible as a module over itself, together with the
trivialization of `O^{⊗ n}` obtained from the canonical identification `O^{⊗ n} ≅ O` followed by
multiplication by `a`. Its trivializations over an object `U` — the local generators `s` of `O`
with `α(s^{⊗ n}) = 1`, which are the sections of the torsor of Tag 040Q's second construction —
are exactly the units `s` of the sections over `U` with `a|_U · sⁿ = 1`, that is with
`sⁿ = (a|_U)⁻¹`; and those are exactly the sections over `U` of the fibre of the `n`-th power map
on the sheaf of units above `a⁻¹`, whose first cohomology class is the Kummer boundary `∂(a⁻¹)`.
Both torsors carry the action of `μ_n` by multiplication by the underlying unit, so the
comparison is an equivariant isomorphism and the two classes agree.

**The convention forces an inverse, not a sign:** the trivializations of the pair are normalized
to the value `1`, while the Kummer torsor of `a` is the sheaf of `n`-th roots *of* `a`, and the
conditions `a·sⁿ = 1` and `xⁿ = a` are exchanged by `a ↦ a⁻¹`. Written additively the inverse is
a negative, which is the second form of the main theorem.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.unitGeneratorOfUnit`: a unit of the sections of the
  structure sheaf is a local generator of the structure sheaf as a module over itself.
* `Stacks.Cohomology.Torsors.Generators.scalarEndOfTerminal` and `scalarIsoOfTerminal`:
  multiplication by a section, respectively a unit, of the structure sheaf over a terminal
  object, as an endomorphism, respectively an automorphism, of a sheaf of modules.
* `Stacks.Cohomology.Torsors.Generators.unitPowIso` is some trivialization of each natural
  tensor power of the structure sheaf, and
  `Stacks.Cohomology.Torsors.Generators.unitPowerTrivialization` is **the canonical one**, the
  one normalized at the section one.
* `Stacks.Cohomology.Torsors.Generators.unitPairTrivialization` is **the trivialization of the
  unit pair at a global unit**, the canonical one twisted by that unit.
* `Stacks.Cohomology.Torsors.Generators.unitPairUnit` and `unitPairOfUnit` pass between the
  trivializations of the unit pair and the units whose `n`-th power inverts the twist.
* `AlgebraicGeometry.restrictUnit` restricts a global unit to an object of the site.
* `AlgebraicGeometry.unitPairToFiber`, `AlgebraicGeometry.fiberToUnitPair` and
  `AlgebraicGeometry.unitPairFiberIso` are the comparison of the sheaf of trivializations of the
  unit pair at `a` with the Kummer fibre of `a⁻¹`, and
  `AlgebraicGeometry.trivializationTorsorHomFiber` reads it as a morphism of torsors.

## Main results

* `Stacks.Cohomology.Torsors.Generators.trivValue_unit_eq`: the trivialization value of a
  section of the structure sheaf is its `n`-th power times the trivialization value of the
  section one, for **any** trivialization of the `n`-th power.
* `Stacks.Cohomology.Torsors.Generators.trivValue_eq_pow_of_trivValue_one`: a trivialization
  whose value at the section one over a terminal object is one takes every section to its `n`-th
  power. This characterizes the canonical trivialization.
* `Stacks.Cohomology.Torsors.Generators.trivValue_unitPowerTrivialization` and
  `trivValue_unitPairTrivialization`: **the trivialization values of the canonical
  trivialization and of the unit pair at `a`** are `sⁿ` and `a|_U · sⁿ`.
* `Stacks.Cohomology.Torsors.Generators.unitPairUnit_spec` and `unitPairOfUnit`: **the
  trivializations of the unit pair at `a` over `U` are exactly the units `s` with
  `a|_U · sⁿ = 1`.**
* `AlgebraicGeometry.pow_eq_restrictUnit_inv_iff` and `AlgebraicGeometry.kummerFiber_mem_iff`:
  **the sections of the Kummer fibre of `a⁻¹` over `U` are exactly the units `x` with
  `xⁿ = (a|_U)⁻¹`.**
* `AlgebraicGeometry.trivializationTorsor_unitPair_isIsomorphic` and
  `trivializationTorsor_unitPair_class_eq`: **the torsor of trivializations of the unit pair at
  `a` is equivariantly isomorphic to the Kummer fibre torsor of `a⁻¹`**, hence has the same
  isomorphism class.
* `AlgebraicGeometry.torsorIsoClassesEquivH1_trivializationTorsor_unitPair`: **the first
  cohomology class of the torsor of trivializations of the unit pair at `a` is the Kummer
  boundary of `a⁻¹`**, and
  `AlgebraicGeometry.torsorIsoClassesEquivH1_trivializationTorsor_unitPair_eq_neg` says the same
  with the inverse read off as a negative, by `AlgebraicGeometry.kummerBoundary_inv`.

## Implementation notes

The trivialization value of a trivialization of `O^{⊗ n}` is **not** computed from the
trivialization. The library's identification `O^{⊗ n} ≅ O`,
`Stacks.SheafOfModules.TensorPower.unitTensorPowerIso`, is built from
`Stacks.Equivalence.powObjIsoSelf` through the iterates of the tensoring autoequivalence and its
quasi-inverse, and has no sectionwise description at all; `unitPowIso` here, built instead by the
recursion through `Stacks.Cohomology.Torsors.Generators.tpowSuccIso` and the right unit
constraint, is no better, since its value on a tensor power of a section would need the value of
the sheafification counit. Both are therefore used only as *some* trivialization, and the value
is obtained by normalizing: for an arbitrary trivialization `al`,
`trivValue al U s = sⁿ · trivValue al U 1` because `s = s · 1` and the `n`-th tensor power of a
scalar multiple is the `n`-th power of the scalar times the tensor power
(`Stacks.Cohomology.Torsors.Generators.powerSection_smul`), and `trivValue al U 1` is the
restriction of `trivValue al T 1` because the trivialization value commutes with restriction and
the section one restricts to the section one. Over a terminal object that value is a unit — it is
the trivialization unit of the local generator one — so composing `al` with multiplication by its
inverse, through `Stacks.SheafOfModules.terminalSectionToEnd`, produces a trivialization whose
value on a section is exactly its `n`-th power. This is the only place the terminal object is
used in the construction, and `trivValue_eq_pow_of_trivValue_one` shows that the normalization
pins the resulting trivialization value down, so that "the canonical `O^{⊗ n} ≅ O`" is
unambiguous as far as the torsor is concerned.

The ring of sections of the structure sheaf of this ringed site over `U` is the ring of global
functions on `F U`, reached through `Stacks.SheafOfModules.Tensor.ringSheaf` and so through a
different spelling, and its units likewise. As in `AlgebraicGeometry.rootUnit` no transport
appears: `Stacks.Cohomology.Torsors.Generators.unitPairUnit_spec` is stated in the ringed site's
spelling and `AlgebraicGeometry.pow_eq_restrictUnit_inv_iff` in the scheme's, and the two are
definitionally equal.

The unit attached to a local generator of the structure sheaf by
`Stacks.Cohomology.Torsors.Generators.isUnit_generatorSections_unit` has that generator as its
underlying section by `rfl`, because `IsUnit.unit` copies the given element into the `val` field.
That is why naturality of the comparison and both of its round trips are `Units.ext rfl`: only
the inverse fields differ, and a unit is determined by its value.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.Torsors (AbelianTorsor torsorSetoid fiberPresheaf fiberPseudoTorsor
  fiberTorsor torsorIsoClassesEquivH1)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible terminalSectionToEnd)
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductRightUnitor)

universe t w v u

namespace Stacks.Cohomology.Torsors.Generators

section Site

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- The sections of the structure sheaf of a ringed site commute. -/
local instance ringSections_isMulCommutative :
    ∀ U, IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (X.O.obj.obj U))

/-- The structure sheaf of a ringed site is invertible as a module over itself. -/
instance isInvertible_unit_ringSheaf :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- A trivialization of every natural tensor power of the structure sheaf, built from the
successor comparison and the right unit constraint. -/
def unitPowIso :
    (k : ℕ) → tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  | 0 => Iso.refl _
  | k + 1 =>
    (tpowSuccIso X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k).symm ≪≫
      tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (unitPowIso k)
          (Iso.refl (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≪≫
        tensorProductRightUnitor X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A unit of the sections of the structure sheaf over an object is a local generator of the
structure sheaf viewed as a module over itself. -/
def unitGeneratorOfUnit (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ) :
    GeneratorSections' X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U := by
  refine ⟨ofUnitVal X U a.val, fun V f => ?_⟩
  obtain ⟨b, hb⟩ := a.isUnit.map
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom.toMonoidHom
  have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.restrictₛₗ f.op
          (ofUnitVal X U a.val)) =
      fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        ofUnitVal X V (r * b.val) := by
    funext r
    exact (unitVal_smul X V r _).trans (congrArg (fun z => r * z)
      ((unitVal_restrict X f (ofUnitVal X U a.val)).trans hb.symm))
  rw [hfun]
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => unitVal X V y * b.inv, fun r => ?_, fun y => ?_⟩
  · exact (mul_assoc r b.val b.inv).trans ((congrArg (fun z => r * z) b.val_inv).trans (mul_one r))
  · exact (mul_assoc (unitVal X V y) b.inv b.val).trans
      ((congrArg (fun z => unitVal X V y * z) b.inv_val).trans (mul_one (unitVal X V y)))

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- The section underlying the local generator attached to a unit is that unit. -/
theorem unitGeneratorOfUnit_val (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ) :
    (unitGeneratorOfUnit X U a).val = ofUnitVal X U a.val := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat] in
/-- A section of the structure sheaf which is a unit is a local generator of the structure
sheaf viewed as a module over itself. -/
theorem generatorSections_property_of_unit (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U))
    (hs : ofUnitVal X U a.val = s) :
    ∀ (V : X.C) (f : V ⟶ U), Function.Bijective
      (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.restrictₛₗ
          f.op s) :=
  hs ▸ (unitGeneratorOfUnit X U a).property

/-- Multiplication by a section of the structure sheaf over a terminal object, as an
endomorphism of a sheaf of modules on a ringed site. -/
def scalarEndOfTerminal {T : X.C} (hT : IsTerminal T)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : M ⟶ M :=
  (terminalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T hT r).asHom.app M

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- On sections it is multiplication by the restricted scalar. -/
theorem scalarEndOfTerminal_app {T : X.C} (hT : IsTerminal T)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (x : M.val.obj (op U)) :
    ((scalarEndOfTerminal X hT r M).val.app (op U)).hom x =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op r • x := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- Composing two such endomorphisms multiplies the scalars. -/
theorem scalarEndOfTerminal_mul {T : X.C} (hT : IsTerminal T)
    (r r' : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    scalarEndOfTerminal X hT r M ≫ scalarEndOfTerminal X hT r' M =
      scalarEndOfTerminal X hT (r * r') M := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op T)))
  ext U x
  let ρ := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op).hom
  change ρ r' • (ρ r • x) = ρ (r * r') • x
  exact (smul_smul (ρ r') (ρ r) x).trans (congrArg (fun z => z • x)
    ((map_mul ρ r' r).symm.trans (congrArg ρ (mul_comm r' r))))

/-- Multiplication by a unit of the sections of the structure sheaf over a terminal object, as
an automorphism of a sheaf of modules on a ringed site. -/
@[ega "0 5.4.7" "partial"]
def scalarIsoOfTerminal {T : X.C} (hT : IsTerminal T)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : M ≅ M where
  hom := scalarEndOfTerminal X hT a.val M
  inv := scalarEndOfTerminal X hT (a⁻¹).val M
  hom_inv_id := by
    refine (scalarEndOfTerminal_mul X hT a.val (a⁻¹).val M).trans ?_
    refine Eq.trans (congrArg (fun z => scalarEndOfTerminal X hT z M) (Units.mul_inv a)) ?_
    ext U x
    change (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op 1 • x = x
    rw [map_one, one_smul]
  inv_hom_id := by
    refine (scalarEndOfTerminal_mul X hT (a⁻¹).val a.val M).trans ?_
    refine Eq.trans (congrArg (fun z => scalarEndOfTerminal X hT z M) (Units.inv_mul a)) ?_
    ext U x
    change (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op 1 • x = x
    rw [map_one, one_smul]

/-- Scaling a section of the structure sheaf scales the trivialization value of its `k`-th
tensor power by the `k`-th power of the scalar. -/
theorem trivValue_unit_smul (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U (r • s) =
      r ^ k *
        trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U s :=
  (congrArg (fun z => unitVal X U ((al.hom.val.app (op U)).hom z))
      (powerSection_smul X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        U r s k)).trans
    ((congrArg (unitVal X U) (((al.hom.val.app (op U)).hom).map_smul (r ^ k)
      (powerSection X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        U s k))).trans
        (unitVal_smul X U (r ^ k) _))

/-- The trivialization value of a section of the structure sheaf is its `k`-th power times the
trivialization value of the section one. -/
theorem trivValue_unit_eq (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U s =
      unitVal X U s ^ k *
        trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U
          (ofUnitVal X U 1) := by
  have hs : (unitVal X U s) • (ofUnitVal X U 1) = s :=
    (unitVal_smul X U (unitVal X U s) (ofUnitVal X U 1)).trans (mul_one (unitVal X U s))
  exact (congrArg
      (trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U)
      hs).symm.trans
    (trivValue_unit_smul X k al U (unitVal X U s) (ofUnitVal X U 1))

/-- The trivialization value at the section one commutes with restriction. -/
theorem trivValue_unit_one_restrict (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al V
        (ofUnitVal X V 1) =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op
        (trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U
          (ofUnitVal X U 1)) :=
  (congrArg (trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al V)
      ((unitVal_restrict X f (ofUnitVal X U 1)).trans (map_one _)).symm).trans
    (trivValue_restrict X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al f
      (ofUnitVal X U 1))

/-- The trivialization unit, over an object of the site, of the section one of the structure
sheaf. -/
def unitPowUnit (T : X.C) (k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ :=
  trivUnit X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k (unitPowIso X k) T
    (unitGeneratorOfUnit X T 1)

/-- Its underlying section is the trivialization value at the section one. -/
theorem unitPowUnit_val (T : X.C) (k : ℕ) :
    (unitPowUnit X T k).val =
      trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
        (unitPowIso X k) T (ofUnitVal X T 1) :=
  trivUnit_val_eq_trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
    (unitPowIso X k) T (unitGeneratorOfUnit X T 1)

/-- The trivialization value of a section over `U` is its `k`-th power times the restriction of
the trivialization value at the section one over a terminal object. -/
private theorem trivValue_unit_eq_map_terminal {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U s =
      unitVal X U s ^ k *
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op
          (trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al T
            (ofUnitVal X T 1)) :=
  (trivValue_unit_eq X k al U s).trans
    (congrArg (fun z => unitVal X U s ^ k * z) (trivValue_unit_one_restrict X k al (hT.from U)))

/-- **A trivialization whose value at the section one over a terminal object is one takes every
section to its `k`-th power.** This is what pins down the canonical trivialization below: it is
normalized at the section one. -/
theorem trivValue_eq_pow_of_trivValue_one {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hal : trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al T
      (ofUnitVal X T 1) = 1)
    (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U s =
      unitVal X U s ^ k :=
  (trivValue_unit_eq_map_terminal X hT k al U s).trans
    ((congrArg (fun z => unitVal X U s ^ k * z)
        ((congrArg ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op)
          hal).trans (map_one _))).trans
      (mul_one _))

/-- **The canonical trivialization of the `k`-th tensor power of the structure sheaf**: the one
whose trivialization value on a section is the `k`-th power of that section. -/
def unitPowerTrivialization {T : X.C} (hT : IsTerminal T) (k : ℕ) :
    tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  unitPowIso X k ≪≫
    scalarIsoOfTerminal X hT (unitPowUnit X T k)⁻¹
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Twisting a trivialization by a global unit multiplies the trivialization value by the
restriction of that unit. -/
theorem trivValue_trans_scalarIsoOfTerminal (k : ℕ)
    (al : tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : X.C} (hT : IsTerminal T)
    (c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
        (al ≪≫ scalarIsoOfTerminal X hT c
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) U s =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op c.val *
        trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k al U s :=
  unitVal_smul X U _ _

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The restriction of a unit times the restriction of its inverse is one. -/
theorem map_inv_mul_map {T U : X.C} (f : U ⟶ T)
    (u : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op (u⁻¹).val *
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op u.val = 1 :=
  (map_mul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom (u⁻¹).val
      u.val).symm.trans
    ((congrArg ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom
      (Units.inv_mul u)).trans (map_one _))

/-- **The canonical trivialization takes a section to its `k`-th power.** -/
theorem trivValue_unitPowerTrivialization {T : X.C} (hT : IsTerminal T) (k : ℕ) (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
        (unitPowerTrivialization X hT k) U s =
      unitVal X U s ^ k := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  have h1 : trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
        (unitPowerTrivialization X hT k) U s =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op
          ((unitPowUnit X T k)⁻¹).val *
        trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
          (unitPowIso X k) U s :=
    trivValue_trans_scalarIsoOfTerminal X k (unitPowIso X k) hT (unitPowUnit X T k)⁻¹ U s
  rw [h1, trivValue_unit_eq_map_terminal X hT k (unitPowIso X k) U s, ← unitPowUnit_val,
    mul_comm (unitVal X U s ^ k), ← mul_assoc, map_inv_mul_map X (hT.from U) (unitPowUnit X T k),
    one_mul]

/-- **The trivialization of the `k`-th tensor power of the structure sheaf attached to a global
unit**: the canonical trivialization twisted by that unit. -/
def unitPairTrivialization {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) :
    tpow X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  unitPowerTrivialization X hT k ≪≫
    scalarIsoOfTerminal X hT a (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Its trivialization value on a section is the unit times the `k`-th power of the
section.** -/
theorem trivValue_unitPairTrivialization {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.C)
    (s : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    trivValue X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
        (unitPairTrivialization X hT k a) U s =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op a.val *
        unitVal X U s ^ k :=
  (trivValue_trans_scalarIsoOfTerminal X k (unitPowerTrivialization X hT k) hT a U s).trans
    (congrArg
      (fun z => (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U).op a.val * z)
      (trivValue_unitPowerTrivialization X hT k U s))

/-- The unit of the sections of the structure sheaf underlying a trivialization of the unit
pair. -/
def unitPairUnit {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
      (unitPairTrivialization X hT k a)).obj U) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U.unop) : Type w)ˣ :=
  (isUnit_generatorSections_unit X U.unop ⟨s.val, s.property.1⟩).unit

/-- Its underlying section is the trivialization itself. -/
theorem unitPairUnit_val {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
      (unitPairTrivialization X hT k a)).obj U) :
    (unitPairUnit X hT k a U s).val = unitVal X U.unop s.val :=
  IsUnit.unit_spec _

/-- **A trivialization of the unit pair is a unit whose `k`-th power inverts the twisting
unit.** -/
theorem unitPairUnit_spec {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.Cᵒᵖ)
    (s : (normalizedSubfunctor X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
      (unitPairTrivialization X hT k a)).obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op a.val *
      (unitPairUnit X hT k a U s).val ^ k = 1 :=
  (congrArg
      (fun z => (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op a.val *
        z ^ k)
      (unitPairUnit_val X hT k a U s)).trans
    ((trivValue_unitPairTrivialization X hT k a U.unop s.val).symm.trans s.property.2)

/-- **Conversely a unit whose `k`-th power inverts the twisting unit is a trivialization of the
unit pair.** -/
def unitPairOfUnit {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U.unop) : Type w)ˣ)
    (hx : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op a.val *
      x.val ^ k = 1) :
    (normalizedSubfunctor X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k
      (unitPairTrivialization X hT k a)).obj U :=
  ⟨ofUnitVal X U.unop x.val,
    generatorSections_property_of_unit X U.unop x (ofUnitVal X U.unop x.val) rfl,
    (trivValue_unitPairTrivialization X hT k a U.unop (ofUnitVal X U.unop x.val)).trans hx⟩

/-- The section underlying such a trivialization is the unit. -/
theorem unitPairOfUnit_val {T : X.C} (hT : IsTerminal T) (k : ℕ)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type w)ˣ) (U : X.Cᵒᵖ)
    (x : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U.unop) : Type w)ˣ)
    (hx : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (hT.from U.unop).op a.val *
      x.val ^ k = 1) :
    (unitPairOfUnit X hT k a U x hx).val = ofUnitVal X U.unop x.val := rfl

end Site

end Stacks.Cohomology.Torsors.Generators

namespace AlgebraicGeometry

section Kummer

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    {T : C} (hT : IsTerminal T) (a : (Scheme.Γ.obj (op (F.obj T)))ˣ)

/-- The restriction of the global unit `a` to an object of the site. -/
abbrev restrictUnit (U : Cᵒᵖ) : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ :=
  Units.map (Scheme.Γ.map (F.map (hT.from U.unop)).op).hom.toMonoidHom a

/-- **The two descriptions of a local `n`-th root of `a⁻¹`**: as a unit whose `n`-th power is
the restriction of `a⁻¹`, and as a unit which normalizes the unit pair at `a`. -/
theorem pow_eq_restrictUnit_inv_iff (U : Cᵒᵖ) (x : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ) :
    x ^ n = restrictUnit F hT a⁻¹ U ↔ (restrictUnit F hT a U).val * x.val ^ n = 1 := by
  have hmap : restrictUnit F hT a⁻¹ U = (restrictUnit F hT a U)⁻¹ :=
    map_inv (Units.map (Scheme.Γ.map (F.map (hT.from U.unop)).op).hom.toMonoidHom) a
  rw [hmap, eq_inv_iff_mul_eq_one, mul_comm (x ^ n), Units.ext_iff, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_one]

/-- **Membership in the Kummer fibre torsor of `a⁻¹`**, for a unit of the sections over an
object of the site. -/
theorem kummerFiber_mem_iff (U : Cᵒᵖ) (x : (Scheme.Γ.obj (op (F.obj U.unop)))ˣ) :
    (kummerSequence J F h n).g.hom.app U (unitsSection F U.unop x) =
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹)).app U ⟨1⟩ ↔
      x ^ n = restrictUnit F hT a⁻¹ U := by
  have hL : (kummerSequence J F h n).g.hom.app U (unitsSection F U.unop x) =
      unitsSection F U.unop (x ^ n) := (ofMul_pow n x).symm
  have hR : (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
        (unitsSection F T a⁻¹)).app U ⟨1⟩ = unitsSection F U.unop (restrictUnit F hT a⁻¹ U) :=
    (terminalSectionMorphism_one _ hT _ U).trans (unitsSection_restrict F (hT.from U.unop) a⁻¹)
  rw [hL, hR]
  exact ⟨fun hx => Additive.ofMul.injective hx, congrArg Additive.ofMul⟩

/-- The trivializations of the unit pair at `a` map to the Kummer fibre torsor of `a⁻¹`. -/
def unitPairToFiber :
    (normalizedSheaf (schemeFunctionsRingedSite J F hO)
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) n
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)).obj ⟶
      fiberPresheaf (kummerSequence J F h n)
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹)) where
  app U := ↾(fun s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO)
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) n
      (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)).obj U =>
    (⟨unitsSection F U.unop
        (unitPairUnit (schemeFunctionsRingedSite J F hO) hT n a U s),
      (kummerFiber_mem_iff J F h n hT a U _).2
        ((pow_eq_restrictUnit_inv_iff F n hT a U _).2
          (unitPairUnit_spec (schemeFunctionsRingedSite J F hO) hT n a U s))⟩ :
      (fiberPresheaf (kummerSequence J F h n)
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹))).obj U))
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ =>
    by exact Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))

/-- The Kummer fibre torsor of `a⁻¹` maps to the trivializations of the unit pair at `a`. -/
def fiberToUnitPair :
    fiberPresheaf (kummerSequence J F h n)
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹)) ⟶
      (normalizedSheaf (schemeFunctionsRingedSite J F hO)
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) n
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)).obj where
  app U := ↾(fun y : (fiberPresheaf (kummerSequence J F h n)
      (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
        (unitsSection F T a⁻¹))).obj U =>
    unitPairOfUnit (schemeFunctionsRingedSite J F hO) hT n a U (Additive.toMul y.1)
      ((pow_eq_restrictUnit_inv_iff F n hT a U (Additive.toMul y.1)).1
        ((kummerFiber_mem_iff J F h n hT a U (Additive.toMul y.1)).1 y.2)))
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ => Subtype.ext rfl

/-- **The trivializations of the unit pair at `a` are the `n`-th roots of `a⁻¹`.** -/
def unitPairFiberIso :
    (normalizedSheaf (schemeFunctionsRingedSite J F hO)
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O)) n
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)).obj ≅
      fiberPresheaf (kummerSequence J F h n)
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹)) where
  hom := unitPairToFiber J F hO h n hT a
  inv := fiberToUnitPair J F hO h n hT a
  hom_inv_id := NatTrans.ext <| funext fun _ => ConcreteCategory.hom_ext _ _ fun _ =>
    Subtype.ext rfl
  inv_hom_id := NatTrans.ext <| funext fun _ => ConcreteCategory.hom_ext _ _ fun _ =>
    by exact Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))

end Kummer

section Comparison

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
    [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{t} (Sheaf J AddCommGrpCat.{u})]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (hS : (kummerSequence J F h n).ShortExact) {T : C} (hT : IsTerminal T)
    (a : (Scheme.Γ.obj (op (F.obj T)))ˣ)

/-- **The comparison of the two torsors is equivariant**: both actions are multiplication by
the unit underlying a section of the sheaf of `n`-th roots of unity. -/
def trivializationTorsorHomFiber :
    (trivializationTorsor J F hO h n hX hroot
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
        (isInvertible_unit_ringSheaf (schemeFunctionsRingedSite J F hO))
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)).1.Hom
      (fiberPseudoTorsor (kummerSequence J F h n) hS
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹))) where
  hom := (unitPairFiberIso J F hO h n hT a).hom
  map_act := by
    intro U g s
    apply Subtype.ext
    have hu : unitPairUnit (schemeFunctionsRingedSite J F hO) hT n a U
          (rootAct J F hO h n (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
            (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a) U
            (Multiplicative.toAdd g) s) =
        rootUnit J F hO h n U (Multiplicative.toAdd g) *
          unitPairUnit (schemeFunctionsRingedSite J F hO) hT n a U s := by
      apply Units.ext
      refine Eq.trans ?_ (Units.val_mul _ _).symm
      refine (unitPairUnit_val (schemeFunctionsRingedSite J F hO) hT n a U _).trans ?_
      refine (rootAct_val J F hO h n
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a) U
        (Multiplicative.toAdd g) s).trans ?_
      refine (unitVal_smul (schemeFunctionsRingedSite J F hO) U.unop
        (rootUnit J F hO h n U (Multiplicative.toAdd g)).val _).trans ?_
      exact congrArg (fun z => (rootUnit J F hO h n U (Multiplicative.toAdd g)).val * z)
        (unitPairUnit_val (schemeFunctionsRingedSite J F hO) hT n a U s).symm
    exact (congrArg Additive.ofMul hu).trans (ofMul_mul _ _)

omit [HasExt (Sheaf J AddCommGrpCat)] in
/-- **The torsor of trivializations of the unit pair at `a` is the Kummer fibre torsor of
`a⁻¹`.** -/
theorem trivializationTorsor_unitPair_isIsomorphic :
    AbelianTorsor.IsIsomorphic
      (trivializationTorsor J F hO h n hX hroot
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
        (isInvertible_unit_ringSheaf (schemeFunctionsRingedSite J F hO))
        (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a))
      (fiberTorsor (kummerSequence J F h n) hS
        (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
          (unitsSection F T a⁻¹))) :=
  ⟨trivializationTorsorHomFiber J F hO h n hX hroot hS hT a,
    inferInstanceAs (IsIso (unitPairFiberIso J F hO h n hT a).hom)⟩

omit [HasExt (Sheaf J AddCommGrpCat)] in
/-- Hence the two torsors have the same isomorphism class. -/
theorem trivializationTorsor_unitPair_class_eq :
    Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
        (trivializationTorsor J F hO h n hX hroot
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
          (isInvertible_unit_ringSheaf (schemeFunctionsRingedSite J F hO))
          (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a)) =
      Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
        (fiberTorsor (kummerSequence J F h n) hS
          (terminalSectionMorphism (kummerSequence J F h n).X₃.obj hT
            (unitsSection F T a⁻¹))) :=
  Quotient.sound (trivializationTorsor_unitPair_isIsomorphic J F hO h n hX hroot hS hT a)

/-- **Stacks Project, Tag 040Q.** The first cohomology class of the torsor of trivializations of
the unit pair at a global unit `a` is the Kummer boundary of `a⁻¹`. -/
theorem torsorIsoClassesEquivH1_trivializationTorsor_unitPair :
    torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
        (Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
          (trivializationTorsor J F hO h n hX hroot
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
            (isInvertible_unit_ringSheaf (schemeFunctionsRingedSite J F hO))
            (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a))) =
      kummerBoundary J F h n hS hT a⁻¹ :=
  (congrArg (torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n))
      (trivializationTorsor_unitPair_class_eq J F hO h n hX hroot hS hT a)).trans
    (terminalBoundary_eq_fiberTorsorClass (kummerSequence J F h n) hS hT
      (unitsSection F T a⁻¹))

/-- The Kummer boundary of the inverse of a global unit is the negative of its boundary. -/
theorem kummerBoundary_inv :
    kummerBoundary J F h n hS hT a⁻¹ = -kummerBoundary J F h n hS hT a := by
  have h0 : kummerBoundary J F h n hS hT a + kummerBoundary J F h n hS hT a⁻¹ = 0 :=
    (kummerBoundary_mul J F h n hS hT a a⁻¹).symm.trans
      ((congrArg (kummerBoundary J F h n hS hT) (mul_inv_cancel a)).trans
        ((kummerBoundary_eq_zero_iff J F h n hS hT 1).2 ⟨1, (one_pow n).symm⟩))
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

/-- **Stacks Project, Tag 040Q, in the additive form.** The same statement with the inverse
read off as a negative in first cohomology. -/
theorem torsorIsoClassesEquivH1_trivializationTorsor_unitPair_eq_neg :
    torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
        (Quotient.mk (torsorSetoid (rootsOfUnitySheaf J F h n))
          (trivializationTorsor J F hO h n hX hroot
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
            (isInvertible_unit_ringSheaf (schemeFunctionsRingedSite J F hO))
            (unitPairTrivialization (schemeFunctionsRingedSite J F hO) hT n a))) =
      -kummerBoundary J F h n hS hT a :=
  (torsorIsoClassesEquivH1_trivializationTorsor_unitPair J F hO h n hX hroot hS hT a).trans
    (kummerBoundary_inv J F h n hS hT a)

end Comparison

end AlgebraicGeometry

end
