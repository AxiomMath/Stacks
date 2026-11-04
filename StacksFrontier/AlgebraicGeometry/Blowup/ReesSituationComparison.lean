module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The two Rees algebra sheaves of a quasi-coherent ideal agree

The repository builds the Rees algebra `⨁_{n ≥ 0} Iⁿ` of a quasi-coherent ideal sheaf twice, as
two relative `Proj` situations over the same scheme.  `Stacks.Blowup.reesSituation` is assembled
from the explicitly given `Stacks.Blowup.reesAlgebraData`, and is the input of the construction
of the blowup of an *algebraic space*.  `AlgebraicGeometry.reesSituation` is assembled from
`AlgebraicGeometry.reesAlgebraData`, which is `Classical.choice` of an existence statement, and
its relative `Proj` is `AlgebraicGeometry.blowUp`, the blowup every geometric fact about blowups
of schemes in this repository is proved for.

This file identifies the two, as schemes over the base.  Nothing can be computed from either
graded algebra directly: one of them is chosen by `Classical.choice`.  What both carry is the
affine-local identification of the degree-`n` sections over an affine open `U` with `I(U)ⁿ` —
the `pieceEquiv` field of the two `ReesAlgebraData` structures — together with the equations
making it multiplicative, unital, compatible with restriction and with the action of the base.
Those five pieces of data are abstracted here into `Stacks.Blowup.ReesModel`, and the comparison
is carried out for an arbitrary model: composing the model's identification with the inverse of
`AlgebraicGeometry.reesPieceEquiv` gives a degreewise isomorphism of graded algebras, which
assembles into an isomorphism of the graded rings of homogeneous local sections over every
affine open, hence of the two relative `Proj` gluing data, hence of the two relative `Proj`s
over the base.

## Main definitions

* `Stacks.Blowup.ReesModel` is a relative `Proj` situation whose homogeneous local sections over
  an affine open are identified with the powers of a quasi-coherent ideal sheaf on its base.
* `Stacks.Blowup.ReesModel.compare` is the degreewise comparison with
  `AlgebraicGeometry.reesSituation`.
* `Stacks.Blowup.ReesModel.sectionRingEquiv` is the induced isomorphism of the graded rings of
  homogeneous local sections over an affine open.
* `Stacks.Blowup.ReesModel.dataIso` is the induced isomorphism of relative-`Proj` gluing data,
  and `Stacks.Blowup.ReesModel.relativeProjIso` the induced isomorphism of relative `Proj`s.
* `Stacks.Blowup.reesSituationModel` exhibits `Stacks.Blowup.reesSituation` as such a model, and
  `Stacks.Blowup.reesSituationBlowUpIso` is the resulting comparison with the blowup.

## Main results

* `Stacks.Blowup.ReesModel.relativeProjIso_hom_toBase` and
  `Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase`: **the isomorphism is an isomorphism
  over the base.**  This is what identifies the two constructions as the same blowup; a bare
  isomorphism of schemes would say nothing.
* `Stacks.Blowup.reesSituationIso`: the same statement in existential form.
* `Stacks.Blowup.isCartierOver_relativeProjToBase_reesSituation` and
  `Stacks.Blowup.exists_nonempty_isTerminal_relativeProj_reesSituation`: Tags 02OS part (2) and
  0806 for the relative `Proj` of `Stacks.Blowup.reesSituation`, obtained by transporting the
  results already proved for `AlgebraicGeometry.blowUp` along the comparison.

## Implementation notes

`AlgebraicGeometry.reesSituation` is an `abbrev`, so instance search sees through it to the base
scheme; `Stacks.Blowup.reesSituation` is a plain definition, and instance search does not unfold
it, so `GradedMonoid.GMul ((Stacks.Blowup.reesSituation I).sectionPieces U n)` and its like are
not found.  That is why the comparison is developed for a *variable* situation and instantiated
only at the end: with the situation a local variable every instance resolves, and instantiating
it later is a single definitional unfolding performed by the elaborator.

Both `pieceEquiv` fields are indexed by `ℤ` and land in `I(U) ^ n.toNat`, while the graded
section rings are indexed by `ℕ`.  `Stacks.Blowup.ReesModel.pieceEquiv` is stated at the `ℕ`
spelling, matching `AlgebraicGeometry.reesPieceEquiv`; the two spellings being definitionally
equal, `Stacks.Blowup.reesSituationModel` converts between them in term mode, once.

Equations between homogeneous sections are checked after applying
`AlgebraicGeometry.reesPieceEquiv` and taking the underlying section of the structure sheaf,
where they are identities in a commutative ring; `Stacks.Blowup.reesPiece_ext` is that
reduction.

The four lemmas in the `Stacks.RelativeProj.Situation` namespace below are the versions of
`AlgebraicGeometry.gradedMul_eq`, `AlgebraicGeometry.gradedOne_eq`,
`AlgebraicGeometry.sectionRingBaseMap_eq` and `AlgebraicGeometry.coe_sectionRingZeroMap` for an
arbitrary situation; the existing ones are stated only for `AlgebraicGeometry.reesSituation`,
and the comparison needs them on both sides.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Stacks.RelativeProj

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- Multiplication of homogeneous sections in the graded section ring is multiplication in the
graded algebra. -/
public theorem gradedMul_eq_algebraMul (U : s.base.Opens) (n m : ℕ)
    (a : s.sectionPieces U n) (b : s.sectionPieces U m) :
    (GradedMonoid.GMul.mul a b : s.sectionPieces U (n + m)) =
      (s.algebra.mul (n : ℤ) (m : ℤ)).app (op U) a b :=
  eq_of_heq ((sectionRingStructure s).mul_homogeneous U n m a b)

/-- The unit of the graded section ring is the unit section of the graded algebra. -/
public theorem gradedOne_eq_algebraOne (U : s.base.Opens) :
    (GradedMonoid.GOne.one : s.sectionPieces U 0) = s.algebra.one.eval (op U) :=
  (sectionRingStructure s).one_homogeneous U

/-- The canonical map from the structure sheaf multiplies the unit section. -/
public theorem sectionRingBaseMap_eq_of_smul_one (U : s.base.Opens)
    (r : s.base.ringCatSheaf.obj.obj (op U)) :
    s.sectionRingBaseMap U r =
      DirectSum.of (s.sectionPieces U) 0 (r • s.algebra.one.eval (op U)) :=
  (sectionRingStructure s).baseMap_apply U r

/-- The degree-zero identification of the graded section ring, read inside the section ring. -/
public theorem coe_sectionRingZeroMap_eq_baseMap (U : s.base.Opens) (r : Γ(s.base, U)) :
    (((sectionRingZeroMap s U).hom r : ↥(s.sectionRingGrading U 0)) : s.sectionRing U) =
      s.sectionRingBaseMap U r := by
  show ((GradedRing.projZeroRingHom' (s.sectionRingGrading U)
    (s.sectionRingBaseMap U r) : s.sectionRing U)) = _
  rw [GradedRing.projZeroRingHom'_apply_coe _
    (⟨s.sectionRingBaseMap U r, sectionRingBaseMap_mem_zero s U r⟩ : s.sectionRingGrading U 0)]

end Stacks.RelativeProj.Situation

namespace Stacks.Blowup

/-! ### Reductions used throughout -/

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Two homogeneous sections of the chosen Rees algebra agree as soon as the underlying
sections of the structure sheaf do.** The degree-`n` identification
`AlgebraicGeometry.reesPieceEquiv` is injective, and so is the inclusion of `I(U)ⁿ` into
`Γ(X, U)`. Every equation between homogeneous sections below is checked through this. -/
public theorem reesPiece_ext (U : X.affineOpens) (n : ℕ)
    {x y : (AlgebraicGeometry.reesSituation I).sectionPieces U.1 n}
    (h : (AlgebraicGeometry.reesPieceEquiv I U n x : Γ(X, U.1)) =
      (AlgebraicGeometry.reesPieceEquiv I U n y : Γ(X, U.1))) : x = y :=
  (AlgebraicGeometry.reesPieceEquiv I U n).injective (Subtype.ext h)

/-! ### Situations realizing the Rees algebra -/

/-- **A relative `Proj` situation realizing the Rees algebra of a quasi-coherent ideal sheaf on
its base.** The data is the identification of the degree-`n` homogeneous local sections over an
affine open `U` with `I(U)ⁿ`; the four equations say that it is multiplicative, unital,
compatible with restriction and compatible with the action of the base. These are exactly the
`pieceEquiv` fields of `Stacks.Blowup.ReesAlgebraData` and of
`AlgebraicGeometry.ReesAlgebraData`, which are distinct structures with identical fields. -/
public structure ReesModel (s : Situation.{u}) (I : s.base.IdealSheafData) where
  /-- The degree-`n` sections over an affine open `U` are `I(U)ⁿ`. -/
  pieceEquiv (U : s.base.affineOpens) (n : ℕ) : s.sectionPieces U.1 n ≃+ ↥(I.ideal U ^ n)
  /-- The identification is multiplicative. -/
  coe_pieceEquiv_mul (U : s.base.affineOpens) (n m : ℕ) (a : s.sectionPieces U.1 n)
      (b : s.sectionPieces U.1 m) :
    ((pieceEquiv U (n + m) ((s.algebra.mul (n : ℤ) (m : ℤ)).app (op U.1) a b)) :
      Γ(s.base, U.1)) =
      (pieceEquiv U n a : Γ(s.base, U.1)) * (pieceEquiv U m b : Γ(s.base, U.1))
  /-- The identification in degree zero sends the unit section to `1`. -/
  coe_pieceEquiv_one (U : s.base.affineOpens) :
    ((pieceEquiv U 0 (s.algebra.one.eval (op U.1))) : Γ(s.base, U.1)) = 1
  /-- The identification commutes with restriction. -/
  coe_pieceEquiv_restrict (U V : s.base.affineOpens) (h : U.1 ≤ V.1) (n : ℕ)
      (a : s.sectionPieces V.1 n) :
    ((pieceEquiv U n ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a)) : Γ(s.base, U.1)) =
      s.base.presheaf.map (homOfLE h).op (pieceEquiv V n a : Γ(s.base, V.1))
  /-- The identification is compatible with the action of the base. -/
  coe_pieceEquiv_smul (U : s.base.affineOpens) (n : ℕ)
      (r : s.base.ringCatSheaf.obj.obj (op U.1)) (a : s.sectionPieces U.1 n) :
    ((pieceEquiv U n (r • a)) : Γ(s.base, U.1)) =
      (show Γ(s.base, U.1) from r) * (pieceEquiv U n a : Γ(s.base, U.1))

namespace ReesModel

variable {s : Situation.{u}} {J : s.base.IdealSheafData} (m : ReesModel s J)

/-! ### The degreewise comparison -/

/-- **A Rees model agrees degreewise with the chosen Rees algebra.** Over an affine open `U` the
degree-`n` sections of either graded algebra are `J(U)ⁿ`, so composing one identification with
the inverse of the other compares them. -/
public def compare (U : s.base.affineOpens) (n : ℕ) :
    s.sectionPieces U.1 n ≃+ (AlgebraicGeometry.reesSituation J).sectionPieces U.1 n :=
  (m.pieceEquiv U n).trans (AlgebraicGeometry.reesPieceEquiv J U n).symm

/-- Reading the comparison through the identification of the target recovers the identification
of the source. -/
public theorem coe_reesPieceEquiv_compare (U : s.base.affineOpens) (n : ℕ)
    (a : s.sectionPieces U.1 n) :
    ((AlgebraicGeometry.reesPieceEquiv J U n (m.compare U n a)) : Γ(s.base, U.1)) =
      (m.pieceEquiv U n a : Γ(s.base, U.1)) := by
  show ((AlgebraicGeometry.reesPieceEquiv J U n
    ((AlgebraicGeometry.reesPieceEquiv J U n).symm (m.pieceEquiv U n a))) :
      Γ(s.base, U.1)) = _
  rw [AddEquiv.apply_symm_apply]

/-- The comparison turns homogeneous multiplication into homogeneous multiplication. -/
public theorem compare_mul (U : s.base.affineOpens) (n p : ℕ) (a : s.sectionPieces U.1 n)
    (b : s.sectionPieces U.1 p) :
    m.compare U (n + p) ((s.algebra.mul (n : ℤ) (p : ℤ)).app (op U.1) a b) =
      ((AlgebraicGeometry.reesSituation J).algebra.mul (n : ℤ) (p : ℤ)).app (op U.1)
        (m.compare U n a) (m.compare U p b) := by
  refine reesPiece_ext J U (n + p) (Eq.trans ?_
    (AlgebraicGeometry.coe_reesPieceEquiv_mul J U n p (m.compare U n a) (m.compare U p b)).symm)
  rw [m.coe_reesPieceEquiv_compare, m.coe_pieceEquiv_mul, m.coe_reesPieceEquiv_compare,
    m.coe_reesPieceEquiv_compare]

/-- The comparison sends the unit section to the unit section. -/
public theorem compare_one (U : s.base.affineOpens) :
    m.compare U 0 (s.algebra.one.eval (op U.1)) =
      (AlgebraicGeometry.reesSituation J).algebra.one.eval (op U.1) := by
  refine reesPiece_ext J U 0
    (Eq.trans ?_ (AlgebraicGeometry.coe_reesPieceEquiv_one J U).symm)
  rw [m.coe_reesPieceEquiv_compare, m.coe_pieceEquiv_one]

/-- The comparison commutes with restriction. -/
public theorem compare_restrict (U V : s.base.affineOpens) (h : U.1 ≤ V.1) (n : ℕ)
    (a : s.sectionPieces V.1 n) :
    m.compare U n ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a) =
      ((AlgebraicGeometry.reesSituation J).algebra.piece (n : ℤ)).val.map (homOfLE h).op
        (m.compare V n a) := by
  refine reesPiece_ext J U n (Eq.trans ?_
    (AlgebraicGeometry.coe_reesPieceEquiv_restrict J U V h n (m.compare V n a)).symm)
  rw [m.coe_reesPieceEquiv_compare U n ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a),
    m.coe_pieceEquiv_restrict U V h n a, m.coe_reesPieceEquiv_compare V n a]

/-- The comparison is compatible with the action of the base. -/
public theorem compare_smul (U : s.base.affineOpens) (n : ℕ)
    (r : s.base.ringCatSheaf.obj.obj (op U.1)) (a : s.sectionPieces U.1 n) :
    m.compare U n (r • a) = r • m.compare U n a := by
  refine reesPiece_ext J U n (Eq.trans ?_
    (AlgebraicGeometry.coe_reesPieceEquiv_smul J U n r (m.compare U n a)).symm)
  rw [m.coe_reesPieceEquiv_compare, m.coe_pieceEquiv_smul, m.coe_reesPieceEquiv_compare]

/-- The comparison matches the units of the two graded section rings. -/
public theorem compare_gradedOne (U : s.base.affineOpens) :
    m.compare U 0 (GradedMonoid.GOne.one : s.sectionPieces U.1 0) =
      (GradedMonoid.GOne.one : (AlgebraicGeometry.reesSituation J).sectionPieces U.1 0) := by
  rw [Situation.gradedOne_eq_algebraOne s U.1,
    Situation.gradedOne_eq_algebraOne (AlgebraicGeometry.reesSituation J) U.1]
  exact m.compare_one U

/-- The comparison matches the multiplications of the two graded section rings. -/
public theorem compare_gradedMul (U : s.base.affineOpens) {n p : ℕ}
    (a : s.sectionPieces U.1 n) (b : s.sectionPieces U.1 p) :
    m.compare U (n + p) (GradedMonoid.GMul.mul a b) =
      GradedMonoid.GMul.mul (m.compare U n a) (m.compare U p b) := by
  rw [Situation.gradedMul_eq_algebraMul s U.1 n p a b,
    Situation.gradedMul_eq_algebraMul (AlgebraicGeometry.reesSituation J) U.1 n p
      (m.compare U n a) (m.compare U p b)]
  exact m.compare_mul U n p a b

/-! ### The comparison of graded section rings over an affine open -/

/-- **The graded rings of homogeneous local sections of the two Rees algebras over an affine open
agree.** The comparison map, as a ring homomorphism. -/
public def sectionHom (U : s.base.affineOpens) :
    s.sectionRing U.1 →+* (AlgebraicGeometry.reesSituation J).sectionRing U.1 :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) n).comp
      (m.compare U n).toAddMonoidHom)
    (by
      change DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) 0
        (m.compare U 0 GradedMonoid.GOne.one) = 1
      rw [m.compare_gradedOne, DirectSum.one_def])
    (fun {n p} a b => by
      change DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) (n + p)
          (m.compare U (n + p) (GradedMonoid.GMul.mul a b)) =
        DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) n
            (m.compare U n a) *
          DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) p
            (m.compare U p b)
      rw [m.compare_gradedMul, DirectSum.of_mul_of])

/-- The comparison map on a homogeneous section. -/
public theorem sectionHom_of (U : s.base.affineOpens) (n : ℕ) (a : s.sectionPieces U.1 n) :
    m.sectionHom U (DirectSum.of (s.sectionPieces U.1) n a) =
      DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) n
        (m.compare U n a) :=
  DirectSum.toSemiring_of _ _ _ n a

/-- The inverse comparison map: decompose into homogeneous parts and apply the degreewise
inverses. -/
public def sectionInv (U : s.base.affineOpens) :
    (AlgebraicGeometry.reesSituation J).sectionRing U.1 →+ s.sectionRing U.1 :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (s.sectionPieces U.1) n).comp (m.compare U n).symm.toAddMonoidHom

/-- The inverse comparison map on a homogeneous section. -/
public theorem sectionInv_of (U : s.base.affineOpens) (n : ℕ)
    (a : (AlgebraicGeometry.reesSituation J).sectionPieces U.1 n) :
    m.sectionInv U (DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) n a) =
      DirectSum.of (s.sectionPieces U.1) n ((m.compare U n).symm a) :=
  DirectSum.toAddMonoid_of _ n a

/-- Additive maps between direct sums whose composite fixes every homogeneous element have
composite the identity. -/
private theorem comp_apply_eq_self_of_of {ι : Type*} [DecidableEq ι] {β γ : ι → Type*}
    [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)] (f : DirectSum ι γ →+ DirectSum ι β)
    (g : DirectSum ι β →+ DirectSum ι γ)
    (h : ∀ i a, f (g (DirectSum.of β i a)) = DirectSum.of β i a) (x : DirectSum ι β) :
    f (g x) = x :=
  DFunLike.congr_fun (DirectSum.addHom_ext (f := f.comp g) (g := AddMonoidHom.id _) h) x

/-- The inverse comparison map undoes the comparison map. -/
public theorem sectionInv_sectionHom (U : s.base.affineOpens) (x : s.sectionRing U.1) :
    m.sectionInv U (m.sectionHom U x) = x :=
  comp_apply_eq_self_of_of (m.sectionInv U) (m.sectionHom U).toAddMonoidHom
    (fun n a ↦ by simp [m.sectionHom_of, m.sectionInv_of]) x

/-- The comparison map undoes the inverse comparison map. -/
public theorem sectionHom_sectionInv (U : s.base.affineOpens)
    (y : (AlgebraicGeometry.reesSituation J).sectionRing U.1) :
    m.sectionHom U (m.sectionInv U y) = y :=
  comp_apply_eq_self_of_of (m.sectionHom U).toAddMonoidHom (m.sectionInv U)
    (fun n a ↦ by simp [m.sectionHom_of, m.sectionInv_of]) y

/-- **The two graded rings of homogeneous local sections over an affine open are isomorphic.** -/
public def sectionRingEquiv (U : s.base.affineOpens) :
    s.sectionRing U.1 ≃+* (AlgebraicGeometry.reesSituation J).sectionRing U.1 where
  toFun := m.sectionHom U
  invFun := m.sectionInv U
  left_inv := m.sectionInv_sectionHom U
  right_inv := m.sectionHom_sectionInv U
  map_add' := (m.sectionHom U).map_add
  map_mul' := (m.sectionHom U).map_mul

/-- The comparison map preserves degrees. -/
public theorem sectionHom_mem (U : s.base.affineOpens) (n : ℕ) {x : s.sectionRing U.1}
    (hx : x ∈ s.sectionRingGrading U.1 n) :
    m.sectionHom U x ∈ (AlgebraicGeometry.reesSituation J).sectionRingGrading U.1 n := by
  obtain ⟨a, rfl⟩ := hx
  rw [m.sectionHom_of]
  exact ⟨_, rfl⟩

/-- The inverse comparison map preserves degrees. -/
public theorem sectionInv_mem (U : s.base.affineOpens) (n : ℕ)
    {y : (AlgebraicGeometry.reesSituation J).sectionRing U.1}
    (hy : y ∈ (AlgebraicGeometry.reesSituation J).sectionRingGrading U.1 n) :
    m.sectionInv U y ∈ s.sectionRingGrading U.1 n := by
  obtain ⟨a, rfl⟩ := hy
  rw [m.sectionInv_of]
  exact ⟨_, rfl⟩

/-- **The comparison isomorphism, as a homomorphism of graded rings.** -/
public def sectionGradedHom (U : s.base.affineOpens) :
    s.sectionRingGrading U.1 →+*ᵍ (AlgebraicGeometry.reesSituation J).sectionRingGrading U.1 where
  toRingHom := m.sectionHom U
  map_mem hx := m.sectionHom_mem U _ hx

/-- **The inverse comparison isomorphism, as a homomorphism of graded rings.** -/
public def sectionGradedHomInv (U : s.base.affineOpens) :
    (AlgebraicGeometry.reesSituation J).sectionRingGrading U.1 →+*ᵍ s.sectionRingGrading U.1 where
  toRingHom := (m.sectionRingEquiv U).symm.toRingHom
  map_mem hy := m.sectionInv_mem U _ hy

/-! ### Naturality and the degree-zero identifications -/

/-- **The comparison is natural in the affine open.** Both composites restrict a homogeneous
section and compare it degreewise. -/
public theorem sectionGradedHom_comp_restrict {U V : s.base.affineOpens} (h : U ≤ V) :
    (m.sectionGradedHom U).comp (Situation.gradedSectionRestriction s U.1 V.1 h) =
      (Situation.gradedSectionRestriction (AlgebraicGeometry.reesSituation J) U.1 V.1 h).comp
        (m.sectionGradedHom V) := by
  refine GradedRingHom.ext fun x ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n a =>
    have hle : U.1 ≤ V.1 := h
    change m.sectionHom U (Situation.gradedSectionRestriction s U.1 V.1 hle _) =
      Situation.gradedSectionRestriction (AlgebraicGeometry.reesSituation J) U.1 V.1 hle
        (m.sectionHom V _)
    rw [Situation.gradedSectionRestriction_of, m.sectionHom_of V]
    erw [m.sectionHom_of U]
    rw [Situation.gradedSectionRestriction_of, m.compare_restrict]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The comparison map sends the image of a section of the structure sheaf to the image of that
same section. -/
public theorem sectionHom_sectionRingBaseMap (U : s.base.affineOpens)
    (r : s.base.ringCatSheaf.obj.obj (op U.1)) :
    m.sectionHom U (s.sectionRingBaseMap U.1 r) =
      (AlgebraicGeometry.reesSituation J).sectionRingBaseMap U.1 r := by
  rw [Situation.sectionRingBaseMap_eq_of_smul_one s U.1 r, m.sectionHom_of, m.compare_smul,
    m.compare_one,
    Situation.sectionRingBaseMap_eq_of_smul_one (AlgebraicGeometry.reesSituation J) U.1 r]

/-- **The comparison is compatible with the two degree-zero identifications with the sections of
the structure sheaf.** -/
public theorem sectionRingZeroMap_comp_sectionGradedHom (U : s.base.affineOpens) :
    Situation.sectionRingZeroMap s U.1 ≫
        CommRingCat.ofHom (m.sectionGradedHom U).gradedZeroRingHom =
      Situation.sectionRingZeroMap (AlgebraicGeometry.reesSituation J) U.1 := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext ?_)
  show m.sectionHom U (((Situation.sectionRingZeroMap s U.1).hom r :
        ↥(s.sectionRingGrading U.1 0)) : s.sectionRing U.1) =
    (((Situation.sectionRingZeroMap (AlgebraicGeometry.reesSituation J) U.1).hom r :
      ↥((AlgebraicGeometry.reesSituation J).sectionRingGrading U.1 0)) :
      (AlgebraicGeometry.reesSituation J).sectionRing U.1)
  rw [Situation.coe_sectionRingZeroMap_eq_baseMap, Situation.coe_sectionRingZeroMap_eq_baseMap]
  exact m.sectionHom_sectionRingBaseMap U r

/-! ### The two relative `Proj`s agree -/

/-- **The two relative-`Proj` gluing data of the Rees algebra of `J` are isomorphic.** Over an
affine open `U` the graded ring is the graded ring of homogeneous sections of one or the other
Rees algebra, and `Stacks.Blowup.ReesModel.sectionGradedHom` identifies them compatibly with
restriction and with the degree-zero identifications. -/
public def dataIso :
    Data.Iso (Situation.chartData s)
      (Situation.chartData (AlgebraicGeometry.reesSituation J)) where
  hom U := m.sectionGradedHom U
  inv U := m.sectionGradedHomInv U
  inv_comp_hom U := GradedRingHom.ext fun x ↦ m.sectionInv_sectionHom U x
  hom_comp_inv U := GradedRingHom.ext fun y ↦ m.sectionHom_sectionInv U y
  hom_comp_restrict h := m.sectionGradedHom_comp_restrict h
  base_comp_hom U := m.sectionRingZeroMap_comp_sectionGradedHom U

/-- **The relative `Proj` of a Rees model of `J` is the blowup of the base in `J`.** -/
public def relativeProjIso : s.relativeProj ≅ AlgebraicGeometry.blowUp J :=
  m.dataIso.relativeProjIso

/-- **The comparison isomorphism is an isomorphism over the base**: it commutes with the two
structure morphisms. This is what identifies the two constructions as the same blowup; a bare
isomorphism of schemes would not. -/
public theorem relativeProjIso_hom_toBase :
    m.relativeProjIso.hom ≫ AlgebraicGeometry.blowUpToBase J = s.relativeProjToBase :=
  m.dataIso.relativeProjIso_hom_toBase

/-- The comparison isomorphism is compatible with the affine charts: over an affine open `U` of
the base it is the comparison of the two charts, `Proj` of the two graded section rings. -/
public theorem relativeProjChart_relativeProjIso_hom (U : s.base.affineOpens) :
    s.relativeProjChart U ≫ m.relativeProjIso.hom =
      (m.dataIso.projIso U).hom ≫ (AlgebraicGeometry.reesSituation J).relativeProjChart U :=
  m.dataIso.chartι_relativeProjIso_hom U

end ReesModel

/-! ### The explicitly built Rees algebra sheaf is such a model -/

/-- **`Stacks.Blowup.reesSituation` realizes the Rees algebra of `I`.** The five components are
the `pieceEquiv` fields of `Stacks.Blowup.ReesAlgebraData`, with the degree converted from its
`ℤ` spelling to its `ℕ` spelling. -/
public def reesSituationModel : ReesModel (Stacks.Blowup.reesSituation I) I where
  pieceEquiv U n := (Stacks.Blowup.reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) U
  coe_pieceEquiv_mul U n p a b :=
    (Stacks.Blowup.reesAlgebraData I).pieceEquiv_mul (n : ℤ) (p : ℤ) (Int.natCast_nonneg n)
      (Int.natCast_nonneg p) U a b
  coe_pieceEquiv_one U := (Stacks.Blowup.reesAlgebraData I).pieceEquiv_one U
  coe_pieceEquiv_restrict U V h n a :=
    (Stacks.Blowup.reesAlgebraData I).pieceEquiv_restrict (n : ℤ) (Int.natCast_nonneg n) U V h a
  coe_pieceEquiv_smul U n r a :=
    (Stacks.Blowup.reesAlgebraData I).pieceEquiv_smul (n : ℤ) (Int.natCast_nonneg n) U r a

/-- **The relative `Proj` of the explicitly built Rees algebra is the blowup.** The relative
`Proj` of `Stacks.Blowup.reesSituation`, which the construction of the blowup of an algebraic
space is built from, is canonically isomorphic to `AlgebraicGeometry.blowUp`, which every
geometric fact about the blowup of a scheme is proved for. The isomorphism is over the base:
see `Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase`. -/
public def reesSituationBlowUpIso :
    (Stacks.Blowup.reesSituation I).relativeProj ≅ AlgebraicGeometry.blowUp I :=
  (reesSituationModel I).relativeProjIso

/-- **The comparison isomorphism of the two Rees algebra situations is an isomorphism over the
base.** -/
public theorem reesSituationBlowUpIso_hom_blowUpToBase :
    (reesSituationBlowUpIso I).hom ≫ AlgebraicGeometry.blowUpToBase I =
      (Stacks.Blowup.reesSituation I).relativeProjToBase :=
  (reesSituationModel I).relativeProjIso_hom_toBase

/-- **The two Rees algebra situations of a quasi-coherent ideal sheaf have the same relative
`Proj` over the base.** The existential form of
`Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase`. -/
public theorem reesSituationIso (J : X.IdealSheafData) :
    ∃ e : (Stacks.Blowup.reesSituation J).relativeProj ≅ AlgebraicGeometry.blowUp J,
      e.hom ≫ AlgebraicGeometry.blowUpToBase J =
        (Stacks.Blowup.reesSituation J).relativeProjToBase :=
  ⟨reesSituationBlowUpIso J, reesSituationBlowUpIso_hom_blowUpToBase J⟩

/-! ### The exceptional divisor of the explicitly built model -/

/-- **Stacks Project, Tag 02OS part (2), for the relative `Proj` of
`Stacks.Blowup.reesSituation`.** The inverse image of the centre `I` along the structure
morphism of `(Stacks.Blowup.reesSituation I).relativeProj` is an effective Cartier divisor, so
that relative `Proj` is an object of the category `C` of Tag 0806.

This is `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal` — the same statement for
`AlgebraicGeometry.blowUp` — transported along `Stacks.Blowup.reesSituationBlowUpIso`: the
comparison being an isomorphism *over the base*, the two inverse-image ideals differ by pullback
along an isomorphism, and an isomorphism is flat
(`Stacks.Divisors.isPullbackDefined_of_flat`).

It is the hypothesis `hb` of `Stacks.Blowup.exists_nonempty_isTerminal_relativeProj` for this
situation. No `@[stacks]` attribute is attached: Tag 02OS part (2) is already claimed by
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`, and this is that result moved to
the other model. -/
public theorem isCartierOver_relativeProjToBase_reesSituation :
    Stacks.Blowup.IsCartierOver I
      (Over.mk (Situation.relativeProjToBase (Stacks.Blowup.reesSituation I))) := by
  show Stacks.Divisors.IsEffectiveCartierDivisor
    (I.comap (Situation.relativeProjToBase (Stacks.Blowup.reesSituation I)))
  rw [← reesSituationBlowUpIso_hom_blowUpToBase I, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat (reesSituationBlowUpIso I).hom
    (I.comap (AlgebraicGeometry.blowUpToBase I))
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)

/-- **Stacks Project, Tag 0806 for the relative `Proj` of `Stacks.Blowup.reesSituation`.** That
relative `Proj`, with its structure morphism, is a terminal object of the category `C` of
objects of `Sch/X` over which the inverse image of the centre is an effective Cartier divisor.

This is `Stacks.Blowup.isTerminal_blowUp` — the same statement for `AlgebraicGeometry.blowUp` —
transported along `Stacks.Blowup.reesSituationBlowUpIso`. The comparison is an isomorphism over
the base, hence an isomorphism in `Over X`; the inclusion of the full subcategory `C` is fully
faithful, so it is an isomorphism in `C`; and terminality transports along an isomorphism.

No `@[stacks]` attribute is attached: Tag 0806 is already claimed by
`Stacks.Blowup.isTerminal_blowUp`, and this is that result moved to the other model. -/
public theorem exists_nonempty_isTerminal_relativeProj_reesSituation :
    ∃ h : Stacks.Blowup.IsCartierOver I
        (Over.mk (Situation.relativeProjToBase (Stacks.Blowup.reesSituation I))),
      Nonempty (IsTerminal
        (⟨Over.mk (Situation.relativeProjToBase (Stacks.Blowup.reesSituation I)), h⟩ :
          Stacks.Blowup.CartierOver I)) := by
  obtain ⟨h₀, ⟨t⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  have hover : (reesSituationBlowUpIso I).inv ≫
      Situation.relativeProjToBase (Stacks.Blowup.reesSituation I) =
      AlgebraicGeometry.blowUpToBase I :=
    (reesSituationBlowUpIso I).inv_comp_eq.2
      (reesSituationBlowUpIso_hom_blowUpToBase I).symm
  exact ⟨isCartierOver_relativeProjToBase_reesSituation I,
    ⟨t.ofIso ((Stacks.Blowup.IsCartierOver I).fullyFaithfulι.preimageIso
      (Over.isoMk (reesSituationBlowUpIso I).symm hover))⟩⟩

end Stacks.Blowup

end
