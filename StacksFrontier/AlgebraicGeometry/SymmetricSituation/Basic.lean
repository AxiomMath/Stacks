module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The symmetric algebra of a sheaf of modules as a relative `Proj` situation

A `Stacks.RelativeProj.Situation` is a scheme together with a graded algebra over its structure
sheaf which is commutative, concentrated in nonnegative degrees, and quasi-coherent in every
degree (Tag 01NN). The projective bundle of Tag 01OB is the relative `Proj` of the symmetric
algebra `Sym(F)` of a sheaf of modules `F`, so to build it one has to produce a `Situation` out
of `SheafOfModules.sheafifiedSymmetricAlgebra`, the symmetric algebra supplied by
`SheafOfModules.tensorExteriorSymmetricAlgebras`.

This file discharges **two of the three conditions** for that algebra, unconditionally and over
an arbitrary ringed site, and reduces the third from all integer degrees to the nonnegative ones:

* commutativity — the symmetric algebra is the degreewise sheafification of the *sectionwise*
  symmetric algebras `U ↦ Sym_{O(U)}(F(U))`, which are commutative rings, and commutativity
  passes through the sheafification because the sheafified multiplication is pinned down on
  local lifts (`Stacks.GradedAlgebra.sheafify_mul_restrict`) and the target is separated;
* vanishing in negative degrees — already available sectionwise;
* quasi-coherence — reduced to the degrees `n ≥ 0`, the negative pieces being zero.

`Stacks.RelativeProj.symmetricSituation` then assembles the `Situation` from quasi-coherence of
the nonnegative symmetric powers alone. That input is the sheaf-theoretic half of Tag 01CK and
is **not** proved here; see the implementation notes.

## Main definitions

* `Stacks.RelativeProj.symmetricSituation`: the symmetric algebra of a sheaf of modules on a
  scheme as a relative `Proj` situation, given quasi-coherence of its nonnegative homogeneous
  pieces.

## Main results

* `Stacks.GradedAlgebra.mul_comm_sheafify`: **graded commutativity transfers to the
  sheafification** of a graded algebra of presheaves of modules. This is the companion of
  `Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` and
  `Stacks.GradedAlgebra.squareZero_sheafifyGen`, which transfer the two *degree-one* side
  conditions; the statement here is the full commutativity in all pairs of degrees, which is
  what Tag 01NN asks of a relative `Proj` algebra.
* `SheafOfModules.mul_comm_sheafifiedSymmetricAlgebra`: the symmetric algebra of a sheaf of
  modules is graded commutative.
* `SheafOfModules.isZero_sheafifiedSymmetricAlgebra_piece_of_neg`: its negative homogeneous
  pieces are zero objects, not merely sectionwise zero.
* `SheafOfModules.isQuasicoherent_sheafifiedSymmetricAlgebra_piece`: quasi-coherence in every
  integer degree follows from quasi-coherence in the nonnegative degrees.

## Implementation notes

**The remaining input.** What `symmetricSituation` takes as a hypothesis is quasi-coherence of
`Symⁿ F` for `n : ℕ`, that is clause (5) of Tag 01CK at the sheaf level. The algebraic side of
that lemma is already available — `SymPow.free_symmetricPower` and
`SymPow.symmetricPower_freePresentation` of
`StacksFrontier/LinearAlgebra/SymmetricPower/FreePresentation.lean` are clauses (6) and the
presentation input (3) of Tag 00DO — and so is the sheafification description of `Symⁿ F`, which
holds here *by construction*: `Stacks.GradedAlgebra.sheafify_piece` says that the degree-`n`
piece of `sheafifiedSymmetricAlgebra` is the sheafification of
`PresheafOfModules.symPowInt n`, which is Tag 01CG on the nose rather than up to a
comparison. Quasi-coherence is a condition on the slice sites
(`SheafOfModules.QuasicoherentData` presents `M.over (X i)`), so using a local trivialization of
`F` requires knowing that `Symⁿ` commutes with restriction to a slice site — the case of
Tag 01CI for an open immersion — and **that is now available**:
`Stacks.SliceAlgebra.symmetricPieceOverIso` of
`StacksFrontier/AlgebraicGeometry/SymmetricSituation/SliceRestriction.lean` is that
isomorphism, degreewise, and `Stacks.SliceAlgebra.isQuasicoherent_piece_of_presentations` is the
resulting reduction. (It is proved there by the two independent halves
`sheafificationRestrictionIso` and `pushforward₀_symmetricAlgebraPiece`, not by
`SheafOfModules.GradedAlgebra.pullbackComparison` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAlgebraPullback.lean`, which is still only
a morphism.) What remains after that reduction is a *presentation* of the degree-`n` symmetric
power of a sheaf of modules admitting one — Tag 01CJ at the sheaf level, whose epimorphy half is
`SheafOfModules.epi_descComp_app_symmetric` of
`StacksFrontier/AlgebraicGeometry/SymmetricSituation/PowerEpi.lean` and whose exactness half is
open — together with Tag 00DN at the sheaf level.

**Where commutativity comes from.** The sectionwise statement is `mul_comm` in
`SymmetricAlgebra R M` read through `PresheafOfModules.symPowIntVal`, whose
injectivity turns the heterogeneous equality the grading forces into an equality of elements of
the symmetric algebra. The transfer to the sheafification is the same three-line pattern as the
`mul_assoc`, `one_mul` and `mul_one` fields of `Stacks.GradedAlgebra.sheafify`: intersect the
two sieves of local lifts, rewrite both products with `sheafify_mul_restrict`, and apply the
sectionwise law under `Stacks.heq_apply`.

**Degrees are `ℤ` and the pieces are a family, so every law is a `HEq`.** `A.mul i j` lands in
`A.piece (i + j)` and `A.mul j i` in `A.piece (j + i)`; these are equal types but not
syntactically so, and `Stacks.heq_of_isSeparated` is the form of separatedness that accepts an
equality of the two sheaves of modules.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite PresheafOfModules

universe v u t a w

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)

/-- **Graded commutativity transfers to the sheafification.** If the multiplication of a graded
algebra of presheaves of modules is commutative on homogeneous local sections, so is the
multiplication of its sheafification. -/
theorem mul_comm_sheafify
    (hc : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
      HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x))
    (i j : ℤ) (X : Cᵒᵖ) (x : ((A.sheafify α).piece i).val.obj X)
    (y : ((A.sheafify α).piece j).val.obj X) :
    HEq (((A.sheafify α).mul i j).app X x y) (((A.sheafify α).mul j i).app X y x) := by
  refine Stacks.heq_of_isSeparated
    (congrArg (fun n : ℤ => (A.sheafify α).piece n) (add_comm i j))
    (J.intersection_covering (liftSieve_mem α (P i) x) (liftSieve_mem α (P j) y)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  rw [A.sheafify_mul_restrict α i j (X := X) f.op x y x₀ y₀ hx₀ hy₀,
    A.sheafify_mul_restrict α j i (X := X) f.op y x y₀ x₀ hy₀ hx₀]
  exact Stacks.heq_apply _ _
    (fun n s => PresheafOfModules.Hom.app (sheafifyUnit α (P n)) (op Y) s) (add_comm i j)
    (hc i j (op Y) x₀ y₀)

end Stacks.GradedAlgebra

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- **The symmetric algebra of a sheaf of modules is graded commutative.** This is the
`mul_comm` condition of a relative `Proj` situation, Tag 01NN. -/
theorem mul_comm_sheafifiedSymmetricAlgebra (i j : ℤ) (U : Cᵒᵖ)
    (a : ((sheafifiedSymmetricAlgebra J F).piece i).val.obj U)
    (b : ((sheafifiedSymmetricAlgebra J F).piece j).val.obj U) :
    HEq (((sheafifiedSymmetricAlgebra J F).mul i j).app U a b)
      (((sheafifiedSymmetricAlgebra J F).mul j i).app U b a) :=
  (PresheafOfModules.symPowIntGradedAlgebra F.val).mul_comm_sheafify
    (𝟙 (toRingCat J Osharp).obj)
    (PresheafOfModules.symPowIntMul_comm F.val) i j U a b

/-- **The negative homogeneous pieces of the symmetric algebra are zero objects.** The
sectionwise statement `symmetricPiece_eq_zero_of_neg_sheafifiedSymmetricAlgebra` says only that
every local section vanishes; this is the `negative_isZero` condition of Tag 01NN. -/
theorem isZero_sheafifiedSymmetricAlgebra_piece_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((sheafifiedSymmetricAlgebra J F).piece n) :=
  (IsZero.iff_id_eq_zero _).2 (by
    ext U x
    exact symmetricPiece_eq_zero_of_neg_sheafifiedSymmetricAlgebra J F n hn U x)

section Quasicoherent

variable [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{w}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Quasi-coherence of the symmetric pieces in every integer degree follows from
quasi-coherence in the nonnegative degrees**, the negative pieces being zero. -/
theorem isQuasicoherent_sheafifiedSymmetricAlgebra_piece
    (hqc : ∀ n : ℕ, ((sheafifiedSymmetricAlgebra J F).piece (n : ℤ)).IsQuasicoherent)
    (n : ℤ) : ((sheafifiedSymmetricAlgebra J F).piece n).IsQuasicoherent := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hqc k
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (isZero_sheafifiedSymmetricAlgebra_piece_of_neg J F n hn)

end Quasicoherent

end SheafOfModules

namespace Stacks.RelativeProj

open _root_.AlgebraicGeometry TopologicalSpace

/-- **The symmetric algebra of a sheaf of modules on a scheme as a relative `Proj` situation.**
Commutativity and vanishing in negative degrees are unconditional; quasi-coherence of the
nonnegative symmetric powers — the sheaf-theoretic clause (5) of Tag 01CK — is the one
hypothesis. The relative `Proj` of this situation is the projective bundle of `F`, Tag 01OB. -/
noncomputable def symmetricSituation (X : Scheme.{u}) (F : X.Modules)
    (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent) :
    Situation.{u} where
  base := X
  algebra := SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) F
  mul_comm := SheafOfModules.mul_comm_sheafifiedSymmetricAlgebra _ F
  negative_isZero n hn :=
    SheafOfModules.isZero_sheafifiedSymmetricAlgebra_piece_of_neg _ F n hn
  isQuasicoherent :=
    SheafOfModules.isQuasicoherent_sheafifiedSymmetricAlgebra_piece _ F hqc

/-- The base of the relative `Proj` situation `symmetricSituation X F hqc` is the scheme `X`. -/
@[simp]
theorem symmetricSituation_base (X : Scheme.{u}) (F : X.Modules)
    (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent) :
    (symmetricSituation X F hqc).base = X := rfl

/-- The graded algebra of `symmetricSituation X F hqc` is the symmetric algebra
`SheafOfModules.sheafifiedSymmetricAlgebra` of `F` over the Zariski site of `X`. -/
@[simp]
theorem symmetricSituation_algebra (X : Scheme.{u}) (F : X.Modules)
    (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent) :
    (symmetricSituation X F hqc).algebra =
      SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) F := rfl

end Stacks.RelativeProj

end
