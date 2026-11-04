module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a sheaf of modules, as a sheaf of graded algebras

`PresheafOfModules.symPowIntGradedAlgebra F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise`) is the
sectionwise symmetric algebra of a presheaf of modules `F`: the graded algebra of presheaves of
modules whose degree-`n` piece is `U ↦ Symⁿ_{O(U)}(F(U))`.
`Stacks.GradedAlgebra.sheafify` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification`) sheafifies a graded
algebra of presheaves of modules degreewise. This file composes the two: the result is the sheaf
of graded algebras that Stacks Section 17.21 calls `Sym(F)`, built — and not merely hypothesised
— together with its degree-one generator, the commutation of that generator's local sections, and
the vanishing of the negative-degree pieces.

## Main definitions

* `PresheafOfModules.symmetricAlgebraSheafify`: **the symmetric algebra of the sheafification of
  `F`**, as a `SheafOfModules.GradedAlgebra`, namely the degreewise sheafification of the
  sectionwise symmetric algebra of `F`.
* `PresheafOfModules.symmetricAlgebraSheafifyGen`: its degree-one generator.
* `PresheafOfModules.symPowIntZeroIso`: the degree-zero identification at the level of presheaves
  of modules, `O ≅ Sym⁰ F`, carrying `1` to the unit of the sectionwise symmetric algebra, with
  `symPowIntZeroHom` and `symPowIntZeroInv` its two directions.

## Main results

* `PresheafOfModules.pairwiseCommutes_symmetricAlgebraSheafifyGen`: the degree-one generator of
  `Sym(F)` has pairwise commuting local sections. This is the first component of
  `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`, and the hypothesis
  `SheafOfModules.TensorExteriorSymmetricAlgebras.pairwiseCommutes_symmetricGenerator` records.
* `PresheafOfModules.symmetricAlgebraSheafify_piece_eq_zero` and
  `isZero_symmetricAlgebraSheafify_piece`: `Sym(F)` has no nonzero local section in a negative
  degree, and its negative-degree pieces are zero objects. These are the
  `symmetricPiece_eq_zero_of_neg` field of
  `SheafOfModules.TensorExteriorSymmetricAlgebras` and the `negative_isZero` field of
  `Stacks.ProjectiveBundle.Situation`.
* `PresheafOfModules.symmetricAlgebraSheafify_mul_comm`: **homogeneous multiplication in `Sym(F)`
  is commutative in every pair of degrees**, which is the `mul_comm` field of
  `Stacks.ProjectiveBundle.Situation`.

## Implementation notes

**What is here and what is not.** This file supplies three of the four symmetric fields of
`SheafOfModules.TensorExteriorSymmetricAlgebras` — `symmetric`, `symmetricGenerator` and
`symmetricPiece_eq_zero_of_neg` — and the first component of the fourth. The *second* component
of `symmetric_isSymmetricAlgebra` is proved one file downstream, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.UniversalProperty`,
where `Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify` is fed the presheaf-level universal
property of the sectionwise algebra; it is kept separate because it needs the comparison map
`Stacks.GradedAlgebra.cmp` and the homogeneity of
`Stacks.GradedAlgebra.liftTotal`, neither of which the three fields above use.

**The degree-zero identification stops at the presheaf level.** `symPowIntZeroIso` identifies
`Sym⁰ F` with `PresheafOfModules.unit` of the base. Transporting it to
`(symmetricAlgebraSheafify α F).piece 0 ≅ SheafOfModules.unit R` — the shape the
`bijective_smul_one` field of `Stacks.ProjectiveBundle.Situation` consumes through
`Stacks.ProjectiveBundle.Situation.bijective_smul_one_of_isoUnit` — additionally needs
`(PresheafOfModules.sheafification α).obj (PresheafOfModules.unit R₀) ≅ SheafOfModules.unit R`,
which is true (the sheafification unit of the free rank-one presheaf of modules is locally
bijective onto the free rank-one sheaf) and is not in the library.

**Universes.** `PresheafOfModules.unit R₀` has its module universe equal to the ring universe, so
the degree-zero section of this file is stated for a presheaf of modules in the ring universe
`w`, while everything above it is stated at the independent module universe `max w a`. That is
the same constraint as the one recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`, and it is forced
by `unit`, not chosen here.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras, carried by
`SheafOfModules.GradedAlgebra`; Tag 01CG is the symmetric-power sheafification statement, which
is not proved here.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w a

namespace PresheafOfModules

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  [HasWeakSheafify J AddCommGrpCat.{max w a}]
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The symmetric algebra of the sheafification of `F`**, as a sheaf of graded algebras: the
degreewise sheafification of the sectionwise symmetric algebra of `F`. Its degree-`n` piece is
the sheafification of `U ↦ Symⁿ_{O(U)}(F(U))`, which is the sheaf Stacks Tag 01CG calls
`Symⁿ F`. -/
@[ega "II 1.7.4" "more general"]
noncomputable def symmetricAlgebraSheafify : SheafOfModules.GradedAlgebra.{w, max w a} R :=
  (symPowIntGradedAlgebra F).sheafify α

/-- **The degree-one generator of `Sym(F)`**: the sheafification of the degree-one generator of
the sectionwise symmetric algebra. -/
noncomputable def symmetricAlgebraSheafifyGen :
    (sheafification α).obj F ⟶ (symmetricAlgebraSheafify α F).piece 1 :=
  (symPowIntGradedAlgebra F).sheafifyGen α (symPowIntGen F)

/-- The degree-`n` piece of `Sym(F)` is the sheafification of the degree-`n` piece of the
sectionwise symmetric algebra of `F`. -/
theorem symmetricAlgebraSheafify_piece (n : ℤ) :
    (symmetricAlgebraSheafify α F).piece n = (sheafification α).obj (symPowInt n F) := rfl

/-- **The degree-one local sections of `Sym(F)` in the image of the generator commute.** This is
the first component of `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`; at the sectionwise
level it is `PresheafOfModules.symPowIntGradedAlgebra_genCommutes`, which holds because the
sectionwise multiplication is that of a commutative ring. -/
theorem pairwiseCommutes_symmetricAlgebraSheafifyGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (symmetricAlgebraSheafifyGen α F) :=
  (symPowIntGradedAlgebra F).pairwiseCommutes_sheafifyGen α (symPowIntGen F)
    (symPowIntGradedAlgebra_genCommutes F)

/-- **`Sym(F)` has no nonzero local section in a negative degree.** This is the
`symmetricPiece_eq_zero_of_neg` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras`: the sectionwise algebra has no sections in a
negative degree, and `Stacks.GradedAlgebra.sheafify_piece_eq_zero` transfers that to the
sheafification. -/
theorem symmetricAlgebraSheafify_piece_eq_zero (n : ℤ) (hn : n < 0) (X : Cᵒᵖ)
    (x : ((symmetricAlgebraSheafify α F).piece n).val.obj X) : x = 0 :=
  (symPowIntGradedAlgebra F).sheafify_piece_eq_zero α n
    (fun Y m => symPowInt_eq_zero_of_neg n F hn Y m) X x

/-- **Homogeneous multiplication in `Sym(F)` is commutative in every pair of degrees.** The
sectionwise multiplication is that of a commutative ring
(`PresheafOfModules.symPowIntMul_comm`), and the sheafified multiplication is read on local lifts
by `Stacks.GradedAlgebra.sheafify_mul_restrict`, so commutativity transfers by separatedness of
the target.

This is the `mul_comm` field of `Stacks.ProjectiveBundle.Situation` and of
`Stacks.RelativeProj.Situation`, and it holds in all degrees rather than only in degree one. -/
theorem symmetricAlgebraSheafify_mul_comm (i j : ℤ) (X : Cᵒᵖ)
    (x : ((symmetricAlgebraSheafify α F).piece i).val.obj X)
    (y : ((symmetricAlgebraSheafify α F).piece j).val.obj X) :
    HEq (((symmetricAlgebraSheafify α F).mul i j).app X x y)
      (((symmetricAlgebraSheafify α F).mul j i).app X y x) := by
  refine Stacks.heq_of_isSeparated
    (congrArg (fun n : ℤ => (sheafification α).obj (symPowInt n F)) (Int.add_comm i j))
    (J.intersection_covering (Stacks.liftSieve_mem α (symPowInt i F) x)
      (Stacks.liftSieve_mem α (symPowInt j F) y)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  have e₁ := (symPowIntGradedAlgebra F).sheafifyMul_restrict α i j (X := X) (Y := op Y) f.op
    x y x₀ y₀ hx₀ hy₀
  have e₂ := (symPowIntGradedAlgebra F).sheafifyMul_restrict α j i (X := X) (Y := op Y) f.op
    y x y₀ x₀ hy₀ hx₀
  exact (heq_of_eq e₁).trans (((Stacks.heq_apply _ _
    (fun n s => Hom.app (sheafifyUnit α (symPowInt n F)) (op Y) s) (Int.add_comm i j)
    (symPowIntMul_comm F i j (op Y) x₀ y₀))).trans (heq_of_eq e₂.symm))

/-- In a negative degree `Sym(F)` has a single local section over every object. -/
theorem subsingleton_symmetricAlgebraSheafify_piece (n : ℤ) (hn : n < 0) (X : Cᵒᵖ) :
    Subsingleton (((symmetricAlgebraSheafify α F).piece n).val.obj X) :=
  ⟨fun x y => (symmetricAlgebraSheafify_piece_eq_zero α F n hn X x).trans
    (symmetricAlgebraSheafify_piece_eq_zero α F n hn X y).symm⟩

/-- **The negative-degree pieces of `Sym(F)` are zero objects.** This is the `negative_isZero`
field of `Stacks.ProjectiveBundle.Situation` and of `Stacks.RelativeProj.Situation`. -/
theorem isZero_symmetricAlgebraSheafify_piece (n : ℤ) (hn : n < 0) :
    IsZero ((symmetricAlgebraSheafify α F).piece n) :=
  (IsZero.iff_id_eq_zero _).2 ((SheafOfModules.forget R).map_injective
    (PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun _x =>
      (subsingleton_symmetricAlgebraSheafify_piece α F n hn X).elim _ _)))

end Sheafify

/-! ### The degree-zero identification -/

section DegreeZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- The degree-zero identification of the sectionwise symmetric algebra, as a morphism of
presheaves of modules out of the free rank-one presheaf: `r ↦ r · 1`. -/
noncomputable def symPowIntZeroHom :
    PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat) ⟶ symPowInt 0 F where
  app X := ModuleCat.ofHom (symPowIntZeroEquiv F X).toLinearMap
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun r =>
    (symPowIntZeroEquiv_naturality F f r).symm)

/-- The inverse of the degree-zero identification, as a morphism of presheaves of modules. -/
noncomputable def symPowIntZeroInv :
    symPowInt 0 F ⟶ PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat) where
  app U := ModuleCat.ofHom (X := (symPowInt 0 F).obj U)
      (Y := (PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat)).obj U)
    { toFun := fun x => (symPowIntZeroEquiv F U).symm x
      map_add' := fun x y => map_add (symPowIntZeroEquiv F U).symm x y
      map_smul' := fun r x => map_smul (symPowIntZeroEquiv F U).symm r x }
  naturality := by
    intro U V f
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨r, rfl⟩ : ∃ r, symPowIntZeroEquiv F U r = x :=
      ⟨(symPowIntZeroEquiv F U).symm x, (symPowIntZeroEquiv F U).apply_symm_apply x⟩
    change (symPowIntZeroEquiv F V).symm ((symPowInt 0 F).map f (symPowIntZeroEquiv F U r)) =
      (O ⋙ forget₂ CommRingCat RingCat).map f
        ((symPowIntZeroEquiv F U).symm (symPowIntZeroEquiv F U r))
    rw [symPowIntZeroEquiv_naturality, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]

/-- **The degree-zero piece of the sectionwise symmetric algebra is the base.** `Sym⁰_{O(U)}(F(U))`
is the image of `O(U)` under the structure map of the symmetric algebra, so the degree-zero piece
is the free rank-one presheaf of modules; `symPowIntZeroIso_hom_one` says the identification
carries `1` to the unit of the algebra.

This is the presheaf-level input to the degree-zero identification of `Sym(F)`; see the
implementation notes for what else that needs. -/
noncomputable def symPowIntZeroIso :
    PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat) ≅ symPowInt 0 F where
  hom := symPowIntZeroHom F
  inv := symPowIntZeroInv F
  hom_inv_id := PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun r =>
      (symPowIntZeroEquiv F U).symm_apply_apply r)
  inv_hom_id := PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      (symPowIntZeroEquiv F U).apply_symm_apply x)

/-- The degree-zero identification carries `1` to the unit of the sectionwise symmetric
algebra. -/
theorem symPowIntZeroIso_hom_one (X : Cᵒᵖ) :
    Hom.app (symPowIntZeroIso F).hom X (1 : (O ⋙ forget₂ CommRingCat RingCat).obj X) =
      (symPowIntOne F).eval X :=
  symPowIntZeroEquiv_one F X

end DegreeZero

end PresheafOfModules
