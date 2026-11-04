module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfASection

/-!
# The trivialization unit of a pair on a ringed site

Let `(C, O)` be a ringed site, `L` an invertible `O`-module and `α : L^{⊗ n} ≅ O` a
trivialization of its `n`-th tensor power. A local generator `s` of `L` over an object `U` has a
tensor power `s^{⊗ n}`, which is a local generator of `L^{⊗ n}`, so `α(s^{⊗ n})` is a local
generator of the structure sheaf over `U`, that is, a unit. This unit — written `trivUnit` below
and `α(s^{⊗ n})` in Tag 040Q — is the whole of the pair `(L, α)` as seen from `s`: scaling `s`
by a unit `a` multiplies it by `aⁿ`, it commutes with restriction, and an isomorphism of pairs
leaves it unchanged. Consequently the local generators on which it takes the value `1` are
permuted simply transitively by the `n`-th roots of unity, which is what makes them a torsor.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.unitVal` and
  `Stacks.Cohomology.Torsors.Generators.ofUnitVal` read a section of the structure sheaf as a
  section of the structure sheaf regarded as a module over itself, and back.
* `Stacks.Cohomology.Torsors.Generators.trivUnit` is the unit `α(s^{⊗ n})`.

## Main results

* `Stacks.Cohomology.Torsors.Generators.isUnit_generatorSections_unit`: a local generator of the
  structure sheaf as a module over itself is a unit.
* `Stacks.Cohomology.Torsors.Generators.trivUnit_val`: the trivialization unit is the value of
  the trivialization on the tensor power of the generator.
* `Stacks.Cohomology.Torsors.Generators.trivUnit_smul`: `α((a·s)^{⊗ n}) = aⁿ · α(s^{⊗ n})`.
* `Stacks.Cohomology.Torsors.Generators.trivUnit_restrict`: it commutes with restriction.
* `Stacks.Cohomology.Torsors.Generators.trivUnit_map`: an isomorphism of invertible modules
  carrying one trivialization to the other preserves it.
* `Stacks.Cohomology.Torsors.Generators.trivUnit_smul_eq_one`: a unit whose `n`-th power
  inverts it normalises the generator.
* `Stacks.Cohomology.Torsors.Generators.existsUnique_rootOfUnity_smul_of_trivUnit_eq`: two local
  generators with the same trivialization unit differ by a unique `n`-th root of unity.

## Implementation notes

The sections of `AlgebraicGeometry.SheafOfModules.unit` of the ring sheaf of the site are the
sections of that sheaf of rings, but not at a spelling instance search sees through: `unitVal`
and `ofUnitVal` are the two type ascriptions, and `unitVal_smul` and `unitVal_restrict` say that
the module structure and the restriction maps are the ring ones.

The ring sheaf of a ringed site is valued in `RingCat`, so the commutativity of its sections is
taken from the `CommRingCat`-valued structure sheaf.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso)
open Stacks.SheafOfModules (IsInvertible)

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- A section of the structure sheaf regarded as a module over itself, read as a section of the
structure sheaf. -/
abbrev unitVal (U : X.C)
    (x : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) := x

/-- A section of the structure sheaf, read as a section of the structure sheaf regarded as a
module over itself. -/
abbrev ofUnitVal (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U) := r

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- Multiplication by a section on the structure sheaf as a module over itself is multiplication
in the structure sheaf. -/
theorem unitVal_smul (U : X.C) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (x : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    unitVal X U (r • x) = r * unitVal X U x := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- Restriction on the structure sheaf as a module over itself is restriction in the structure
sheaf. -/
theorem unitVal_restrict {U V : X.C} (f : V ⟶ U)
    (x : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj (op U)) :
    unitVal X V
        ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.restrictₛₗ f.op x) =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op (unitVal X U x) := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- A local generator of the structure sheaf, viewed as a module over itself, is a unit. -/
theorem isUnit_generatorSections_unit (U : X.C)
    (s : GeneratorSections' X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :
    IsUnit (unitVal X U s.val) := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  have h := s.property U (𝟙 U)
  have he :
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.restrictₛₗ (𝟙 U).op
        s.val = s.val := by
    show ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (𝟙 (op U))) (unitVal X U s.val) =
      unitVal X U s.val
    rw [(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id]
    rfl
  rw [he] at h
  obtain ⟨r, hr⟩ := h.2 (ofUnitVal X U 1)
  have hr' : r * unitVal X U s.val = 1 := hr
  exact ⟨⟨unitVal X U s.val, r, (mul_comm (unitVal X U s.val) r).trans hr', hr'⟩, rfl⟩

/-- The unit of the structure sheaf comparing a trivialization of the `n`-th tensor power of an
invertible module with the `n`-th tensor power of a local generator. -/
noncomputable def trivUnit (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ :=
  (isUnit_generatorSections_unit X U
    (generatorSections_mapIso' X al U (generatorPowerSection X L U s n))).unit

/-- The trivialization unit is the value of the trivialization on the tensor power of the
generator. -/
theorem trivUnit_val (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s : GeneratorSections' X L U) :
    (trivUnit X L n al U s).val =
      unitVal X U ((al.hom.val.app (op U)).hom (powerSection X L U s.val n)) :=
  (IsUnit.unit_spec _).trans (congrArg (fun z => unitVal X U ((al.hom.val.app (op U)).hom z))
    (generatorPowerSection_val X L U s n))

/-- Scaling a local generator by a unit scales the trivialization unit by its `n`-th power. -/
theorem trivUnit_smul (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ)
    (s : GeneratorSections' X L U) :
    trivUnit X L n al U (generatorSections_smul_unit' X L U a s) =
      a ^ n * trivUnit X L n al U s := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, trivUnit_val, trivUnit_val]
  have hval : (generatorSections_smul_unit' X L U a s).val = a.val • s.val := rfl
  rw [hval, powerSection_smul]
  exact congrArg (unitVal X U) (((al.hom.val.app (op U)).hom).map_smul _ _)

/-- The trivialization unit commutes with restriction. -/
theorem trivUnit_restrict (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : V ⟶ U)
    (s : GeneratorSections' X L U) :
    (trivUnit X L n al V (generatorSections_restrict' X L f s)).val =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op (trivUnit X L n al U s).val := by
  rw [trivUnit_val, trivUnit_val]
  have hval : (generatorSections_restrict' X L f s).val = L.val.restrictₛₗ f.op s.val := rfl
  rw [hval, ← powerSection_restrict]
  exact congrArg (unitVal X V)
    (PresheafOfModules.naturality_apply al.hom.val f.op (powerSection X L U s.val n))

/-- An isomorphism of invertible modules compatible with two trivializations of the `n`-th
tensor powers matches their trivialization units. -/
theorem trivUnit_map {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (be : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (e : L ≅ M)
    (hc : powerMap X e n ≪≫ be = al) (U : X.C) (s : GeneratorSections' X L U) :
    trivUnit X M n be U (generatorSections_mapIso' X e U s) = trivUnit X L n al U s := by
  apply Units.ext
  rw [trivUnit_val, trivUnit_val]
  have hval : (generatorSections_mapIso' X e U s).val = (e.hom.val.app (op U)).hom s.val := rfl
  rw [hval, ← powerSection_map X e U s.val n, comp_val_app_apply]
  exact congrArg
    (fun z : tpow X L n ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) =>
    unitVal X U ((z.val.app (op U)).hom (powerSection X L U s.val n)))
    (congrArg Iso.hom hc)

/-- A unit scaling the trivialization unit to one normalises the generator. -/
theorem trivUnit_smul_eq_one (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (b : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ)
    (s : GeneratorSections' X L U)
    (hb : b ^ n * trivUnit X L n al U s = 1) :
    trivUnit X L n al U (generatorSections_smul_unit' X L U b s) = 1 :=
  (trivUnit_smul X L n al U b s).trans hb

/-- Two local generators with the same trivialization unit differ by a unique `n`-th root of
unity. -/
theorem existsUnique_rootOfUnity_smul_of_trivUnit_eq
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (s t : GeneratorSections' X L U)
    (h : trivUnit X L n al U s = trivUnit X L n al U t) :
    ∃! a : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w)ˣ,
      a ^ n = 1 ∧ generatorSections_smul_unit' X L U a s = t := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) : Type w) :=
    inferInstanceAs (CommRing (X.O.obj.obj (op U)))
  obtain ⟨a, ha, hau⟩ := existsUnique_unit_smul_generatorSections' X L U s t
  have hst : generatorSections_smul_unit' X L U a s = t := Subtype.ext ha
  have hpow : a ^ n = 1 := mul_eq_right.1
    ((trivUnit_smul X L n al U a s).symm.trans
      ((congrArg (trivUnit X L n al U) hst).trans h.symm))
  exact ⟨a, ⟨hpow, hst⟩, fun b hb ↦ hau b (congrArg Subtype.val hb.2)⟩

end Stacks.Cohomology.Torsors.Generators

end
