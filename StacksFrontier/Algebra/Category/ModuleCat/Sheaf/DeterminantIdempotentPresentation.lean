module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SigmaFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleIdempotentRetract

/-!
# The determinant is of finite presentation where the rank idempotents trivialise it

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it, `F` a sheaf of modules over the
underlying sheaf of rings and `A` a package of tensor, exterior and symmetric algebras of `F` in
the sense of Section 17.21. This file proves that the determinant `det(F)` of [Stacks, Tag 0FJN] is
of finite presentation, given on each member `U` of a covering family:

* `F|_U` as a retract of a finite free sheaf of modules, as in Stacks 08BL
  (`Stacks.SheafOfModules.IsLocallyFiniteFreeSummand`);
* a family `eₙ` of compatible local scalars on `U` such that multiplication by `eₙ` carries
  `⋀ⁿ(F|_U)` into the degree-`n` exterior annihilator and is the identity on it;
* the vanishing of the degree-`n` annihilator outside a finite set of degrees.

On the module side `eₙ` is the idempotent of Stacks 0FJ9 cutting out the rank-`n` stratum of
`Γ(U, F)`, and the two conditions on it are
`ProjectiveDeterminant.rankIdempotent_smul_eq_zero_of_mem_exteriorPower` and
`ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart`. Here the two conditions
are stated on local sections, and the `eₙ` are not assumed to be idempotent.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerRetractFree`: **every exterior
  power of a retract of a finite free sheaf of modules is a retract of a finite free sheaf of
  modules.**

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.retract_exteriorAnnihilator_free`: the
  degree-`n` exterior annihilator is a retract of a finite free sheaf of modules, where `eₙ`
  acts as described.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exists_isFinite_presentation_determinant_over`:
  **the determinant has a finite presentation on a trivialising open.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isFinitePresentation_determinant_of_coversTop`:
  **the determinant is of finite presentation**, for a covering family of trivialising opens.

## Implementation notes

The linear order on the index type that Mathlib's exterior basis needs is supplied by well-ordering
the index type, so it does not appear in the statements about the determinant.

The determinant is an `ℕ`-indexed coproduct, and `ℕ` is not in the module universe, so the
surviving degrees are enumerated by `ULift {n // n ∈ s}`, a type in the module universe.

The hypotheses on a member `U` of the covering family are stated for a package for `F|_U` on the
slice site, related to `det(F)|_U` by
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantOverIso`.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v u

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The exterior power of a retract of a finite free sheaf of modules -/

section ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {G : SheafOfModules.{w} (toRingCat J Osharp)} (B : TensorExteriorSymmetricAlgebras J G)
  {ι : Type w} [Finite ι]
  (B' : TensorExteriorSymmetricAlgebras J
    (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι))

/-- The degree-`n` exterior power of a retract is a retract of the degree-`n` exterior power, by
the images of the two morphisms under `⋀ⁿ`. -/
def exteriorPowerRetract
    (ρ : Retract G (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι)) (n : ℕ) :
    Retract (B.exteriorPower n) (B'.exteriorPower n) where
  i := B.exteriorPowerMap B' ρ.i (n : ℤ)
  r := B'.exteriorPowerMap B ρ.r (n : ℤ)
  retract := by
    rw [← exteriorPowerMap_comp B B' B ρ.i ρ.r (n : ℤ), ρ.retract, exteriorPowerMap_id]

/-- **Every exterior power of a sheaf of modules which is a retract of a finite free sheaf of
modules is a retract of a finite free sheaf of modules**, the free sheaf of modules on the
`n`-element subsets of the index type. -/
def exteriorPowerRetractFree [LinearOrder ι]
    (ρ : Retract G (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι)) (n : ℕ) :
    Retract (B.exteriorPower n)
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) (Set.powersetCard ι n)) :=
  (exteriorPowerRetract B B' ρ n).trans
    (Retract.ofIso (Stacks.SheafOfModules.exteriorPowerFreeIso J n B'))

end ExteriorPower

/-! ### The annihilator where the idempotents act -/

section Annihilator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {G : SheafOfModules.{w} (toRingCat J Osharp)} (B : TensorExteriorSymmetricAlgebras J G)

/-- The rings of sections of the underlying sheaf of rings of a sheaf of commutative rings are
commutative. -/
instance isMulCommutative_toRingCat (V : Cᵒᵖ) :
    IsMulCommutative ((toRingCat J Osharp).obj.obj V) :=
  inferInstanceAs (IsMulCommutative (Osharp.obj.obj V))

variable (f : ((toRingCat J Osharp).obj ⋙ CategoryTheory.forget RingCat).sections) (n : ℕ)

/-- **The degree-`n` exterior annihilator is a retract of a finite free sheaf of modules**, when
multiplication by `f` maps the degree-`n` exterior power into the annihilator and is the identity
on it, and the sheaf of modules is a retract of a finite free one. -/
def retract_exteriorAnnihilator_free {ι : Type w} [Finite ι]
    (B' : TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι))
    (ρ : Retract G (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι)) [LinearOrder ι]
    (hmem : ∀ (V : Cᵒᵖ) (x : (B.exteriorPower n).val.obj V),
      f.val V • x ∈ (B.exteriorAnnihilator n).obj V)
    (hself : ∀ (V : Cᵒᵖ) (y : (B.exteriorAnnihilator n).obj V),
      f.val V • (y : (B.exteriorPower n).val.obj V) = (y : (B.exteriorPower n).val.obj V)) :
    Retract (B.exteriorAnnihilator n).toSheafOfModules
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) (Set.powersetCard ι n)) :=
  (Stacks.SheafOfModules.retractOfSmul (toRingCat J Osharp) (B.exteriorAnnihilator n) f hmem
    hself).trans (exteriorPowerRetractFree B B' ρ n)

end Annihilator

/-! ### The determinant on a trivialising open -/

section Over

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {G : SheafOfModules.{w} (toRingCat J Osharp)} (B : TensorExteriorSymmetricAlgebras J G)

/-- **The determinant of a sheaf of modules which is a retract of a finite free sheaf of modules
has a finite presentation**, given scalars `f n` such that multiplication by `f n` maps the
degree-`n` exterior power into the degree-`n` exterior annihilator and is the identity on it, and a
finite set `s` outside which the exterior annihilators vanish. -/
theorem exists_isFinite_presentation_determinant_of_idempotents {ι : Type w} [Finite ι]
    (B' : TensorExteriorSymmetricAlgebras J
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι))
    (ρ : Retract G (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι))
    (f : ℕ → ((toRingCat J Osharp).obj ⋙ CategoryTheory.forget RingCat).sections) (s : Finset ℕ)
    (hz : ∀ n ∉ s, IsZero (B.exteriorAnnihilator n).toSheafOfModules)
    (hmem : ∀ (n : ℕ) (V : Cᵒᵖ) (x : (B.exteriorPower n).val.obj V),
      (f n).val V • x ∈ (B.exteriorAnnihilator n).obj V)
    (hself : ∀ (n : ℕ) (V : Cᵒᵖ) (y : (B.exteriorAnnihilator n).obj V),
      (f n).val V • (y : (B.exteriorPower n).val.obj V) = (y : (B.exteriorPower n).val.obj V)) :
    ∃ p : B.determinant.Presentation, p.IsFinite := by
  classical
  let _ : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  refine Stacks.SheafOfModules.exists_isFinite_presentation_sigma_of_isZero_of_retract_free
    (G := fun n : ℕ => (B.exteriorAnnihilator n).toSheafOfModules) (fun n : ℕ => n ∈ s) hz
    (T := ULift.{w} {n : ℕ // n ∈ s}) (Equiv.ulift.{w} (α := {n : ℕ // n ∈ s}))
    (fun t => (Set.powersetCard ι (Equiv.ulift.{w} t).1))
    fun t => retract_exteriorAnnihilator_free B (f (Equiv.ulift.{w} t).1)
      (Equiv.ulift.{w} t).1 B' ρ (hmem _) (hself _)

/-- **The determinant of `F` restricted to `U` has a finite presentation**, given a package `B` for
`F|_U` on the slice site, `F|_U` as a retract of a finite free sheaf of modules, and scalars as in
`exists_isFinite_presentation_determinant_of_idempotents` for `B`. -/
theorem exists_isFinite_presentation_determinant_over
    {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)
    (U : C) [HasBinaryProducts C]
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over U) AddCommGrpCat.{w}]
    (B : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over U) (J.over U) (F.over U))
    {ι : Type w} [Finite ι]
    (B' : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over U) (J.over U)
      (_root_.SheafOfModules.free (R := toRingCat (J.over U) (Osharp.over U)) ι))
    (ρ : Retract (F.over U)
      (_root_.SheafOfModules.free (R := toRingCat (J.over U) (Osharp.over U)) ι))
    (f : ℕ → ((toRingCat (J.over U) (Osharp.over U)).obj ⋙
      CategoryTheory.forget RingCat).sections) (s : Finset ℕ)
    (hz : ∀ n ∉ s, IsZero (B.exteriorAnnihilator n).toSheafOfModules)
    (hmem : ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (x : (B.exteriorPower n).val.obj V),
      (f n).val V • x ∈ (B.exteriorAnnihilator n).obj V)
    (hself : ∀ (n : ℕ) (V : (Over U)ᵒᵖ) (y : (B.exteriorAnnihilator n).obj V),
      (f n).val V • (y : (B.exteriorPower n).val.obj V) = (y : (B.exteriorPower n).val.obj V)) :
    ∃ p : (A.determinant.over U).Presentation, p.IsFinite := by
  obtain ⟨p, hp⟩ := exists_isFinite_presentation_determinant_of_idempotents B B' ρ f s hz hmem
    hself
  exact ⟨Stacks.SheafOfModules.presentationOfIso (determinantOverIso A U B).symm p,
    Stacks.SheafOfModules.presentationOfIso_isFinite _ _ (hP := hp)⟩

end Over

/-! ### The conclusion -/

section CoversTop

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasBinaryProducts C]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]

/-- **The determinant of a sheaf of modules is of finite presentation** if each member of a
covering family carries the data of `exists_isFinite_presentation_determinant_over`. -/
theorem isFinitePresentation_determinant_of_coversTop
    {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)
    {I : Type*} (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, ∃ (B : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over (X i))
        (J.over (X i)) (F.over (X i))) (κ : Type w) (_ : Finite κ)
        (_ : TensorExteriorSymmetricAlgebras (Osharp := Osharp.over (X i)) (J.over (X i))
          (_root_.SheafOfModules.free
            (R := toRingCat (J.over (X i)) (Osharp.over (X i))) κ))
        (_ : Retract (F.over (X i))
          (_root_.SheafOfModules.free
            (R := toRingCat (J.over (X i)) (Osharp.over (X i))) κ))
        (f : ℕ → ((toRingCat (J.over (X i)) (Osharp.over (X i))).obj ⋙
          CategoryTheory.forget RingCat).sections)
        (s : Finset ℕ),
      (∀ n ∉ s, IsZero (B.exteriorAnnihilator n).toSheafOfModules) ∧
      (∀ (n : ℕ) (V : (Over (X i))ᵒᵖ) (x : (B.exteriorPower n).val.obj V),
        (f n).val V • x ∈ (B.exteriorAnnihilator n).obj V) ∧
      (∀ (n : ℕ) (V : (Over (X i))ᵒᵖ) (y : (B.exteriorAnnihilator n).obj V),
        (f n).val V • (y : (B.exteriorPower n).val.obj V) =
          (y : (B.exteriorPower n).val.obj V))) :
    A.determinant.IsFinitePresentation := by
  refine Stacks.SheafOfModules.isFinitePresentation_of_coversTop X hX fun i => ?_
  obtain ⟨B, κ, _, B', ρ, f, s, hz, hmem, hself⟩ := h i
  exact exists_isFinite_presentation_determinant_over A (X i) B B' ρ f s hz hmem hself

end CoversTop

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
