module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DataIso

/-!
# The two Rees algebras of a quasi-coherent ideal sheaf agree

The blowup of a scheme `X` in a quasi-coherent ideal sheaf `I` is the relative `Proj` of the Rees
algebra `⨁_{n ≥ 0} Iⁿ`, and that Rees algebra admits two descriptions. Globally it is a graded
sheaf of algebras over the structure sheaf, `AlgebraicGeometry.reesAlgebraData`, and the relative
`Proj` of such a sheaf is glued from the `Proj` of its graded rings of homogeneous local sections
(`AlgebraicGeometry.blowUp`). Affine-locally it is the ordinary Rees algebra `Γ(X, U)[I(U)t]` of
the ideal `I(U)`, with its grading by the degree of a polynomial, and the relative `Proj` of that
family is glued directly (`Stacks.Blowup.blowUp`).

This file identifies the two. Over an affine open `U` the degree-`n` piece of either graded ring
is `I(U)ⁿ`: on the sheaf side by `AlgebraicGeometry.ReesAlgebraData.pieceEquiv`, on the polynomial
side by `Stacks.Blowup.reesGradingEquivPow`. Composing gives a degreewise isomorphism, which
assembles into an isomorphism of graded rings and then — the two gluing data being isomorphic — to
an isomorphism of the two blowups **over `X`**.

## Main definitions

* `AlgebraicGeometry.reesPieceEquiv` identifies the degree-`n` sections of the Rees algebra sheaf
  over an affine open `U` with `I(U)ⁿ`, at a `ℕ`-valued degree.
* `AlgebraicGeometry.reesGradedPieceEquiv` identifies them with the degree-`n` part of
  `Γ(X, U)[I(U)t]`.
* `AlgebraicGeometry.reesSectionRingEquiv` is the resulting ring isomorphism between the graded
  ring of homogeneous local sections over `U` and the ordinary Rees algebra of `I(U)`.
* `AlgebraicGeometry.reesSectionGradedHom` and `AlgebraicGeometry.reesSectionGradedHomInv` are
  that isomorphism and its inverse as homomorphisms of graded rings.
* `AlgebraicGeometry.reesDataIso` is the induced isomorphism of relative-`Proj` gluing data.
* `AlgebraicGeometry.blowUpIso` is the induced isomorphism of the two blowups.

## Main results

* `AlgebraicGeometry.reesSectionGradedHom_comp_gradedSectionRestriction`: the comparison is
  natural in the affine open.
* `AlgebraicGeometry.sectionRingZeroMap_comp_reesSectionGradedHom`: it is compatible with the two
  degree-zero identifications with `Γ(X, U)`.
* `AlgebraicGeometry.blowUpIso_hom_blowUpToBase`: **the isomorphism of blowups is an isomorphism
  over `X`.** This is what makes the two constructions the same blowup; a bare isomorphism of
  schemes would say nothing.

## Implementation notes

The sheaf-side Rees algebra is selected by `Classical.choice` from
`Stacks.Blowup.exists_reesAlgebraData`, so nothing can be computed from the chosen witness.
What is available is the defining characterisation carried by
`AlgebraicGeometry.ReesAlgebraData`: an additive identification of the degree-`n` sections over an
affine open with `I(U)ⁿ`, together with the equations making it multiplicative, unital, compatible
with restriction and with the action of the base. Every lemma here is deduced from those five
fields and nothing else.

Both sides spell the degree in a different way, and that is the one real friction. The sheaf-side
pieces are indexed by `ℤ` and the identification lands in `I(U) ^ n.toNat`; the polynomial side is
indexed by `ℕ`. `AlgebraicGeometry.reesPieceEquiv` pins the `ℕ` spelling once, by ascription, and
every subsequent lemma is stated in it and proved by `exact` against the corresponding field of
`AlgebraicGeometry.ReesAlgebraData` — the two spellings being definitionally equal, this is where
the conversion happens, once, in term mode. In particular `(↑(n + m) : ℤ)` and `(↑n + ↑m : ℤ)` are
reconciled inside `AlgebraicGeometry.coe_reesPieceEquiv_mul` rather than at every use.

Equations between elements of the Rees algebra are checked on the underlying polynomial, where
they are identities between monomials in a commutative ring.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
  Stacks.RelativeProj Stacks.Blowup

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The degree-`n` identifications -/

/-- **The degree-`n` sections of the Rees algebra sheaf over an affine open are `Iⁿ`.** This is
`AlgebraicGeometry.ReesAlgebraData.pieceEquiv` with the degree pinned at its `ℕ` spelling: the
field is indexed by `ℤ` and lands in `I(U) ^ n.toNat`, and the ascription here fixes one spelling
for the whole file. -/
public def reesPieceEquiv (U : X.affineOpens) (n : ℕ) :
    (reesSituation I).sectionPieces U.1 n ≃+ ↥(I.ideal U ^ n) :=
  (reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) U

/-- The identifications are multiplicative. -/
public theorem coe_reesPieceEquiv_mul (U : X.affineOpens) (n m : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) (b : (reesSituation I).sectionPieces U.1 m) :
    ((reesPieceEquiv I U (n + m)
        (((reesSituation I).algebra.mul (n : ℤ) (m : ℤ)).app (op U.1) a b) : Γ(X, U.1))) =
      (reesPieceEquiv I U n a : Γ(X, U.1)) * (reesPieceEquiv I U m b : Γ(X, U.1)) :=
  (reesAlgebraData I).pieceEquiv_mul (n : ℤ) (m : ℤ) (Int.natCast_nonneg n)
    (Int.natCast_nonneg m) U a b

/-- The identification in degree zero sends the unit section to `1`. -/
public theorem coe_reesPieceEquiv_one (U : X.affineOpens) :
    ((reesPieceEquiv I U 0 ((reesSituation I).algebra.one.eval (op U.1)) : Γ(X, U.1))) = 1 :=
  (reesAlgebraData I).pieceEquiv_one U

/-- The identifications commute with restriction. -/
public theorem coe_reesPieceEquiv_restrict (U V : X.affineOpens) (h : U.1 ≤ V.1) (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    ((reesPieceEquiv I U n
        (((reesSituation I).algebra.piece (n : ℤ)).val.map (homOfLE h).op a) : Γ(X, U.1))) =
      X.presheaf.map (homOfLE h).op (reesPieceEquiv I V n a : Γ(X, V.1)) :=
  (reesAlgebraData I).pieceEquiv_restrict (n : ℤ) (Int.natCast_nonneg n) U V h a

/-- The identifications are compatible with the action of the base. -/
public theorem coe_reesPieceEquiv_smul (U : X.affineOpens) (n : ℕ)
    (r : X.ringCatSheaf.obj.obj (op U.1)) (a : (reesSituation I).sectionPieces U.1 n) :
    ((reesPieceEquiv I U n (r • a) : Γ(X, U.1))) =
      (show Γ(X, U.1) from r) * (reesPieceEquiv I U n a : Γ(X, U.1)) :=
  (reesAlgebraData I).pieceEquiv_smul (n : ℤ) (Int.natCast_nonneg n) U r a

/-- Multiplication of homogeneous sections in the graded section ring is multiplication in the
graded algebra. -/
public theorem gradedMul_eq (U : X.affineOpens) (n m : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) (b : (reesSituation I).sectionPieces U.1 m) :
    (GradedMonoid.GMul.mul a b : (reesSituation I).sectionPieces U.1 (n + m)) =
      ((reesSituation I).algebra.mul (n : ℤ) (m : ℤ)).app (op U.1) a b :=
  eq_of_heq ((Situation.sectionRingStructure (reesSituation I)).mul_homogeneous U.1 n m a b)

/-- The unit of the graded section ring is the unit section of the graded algebra. -/
public theorem gradedOne_eq (U : X.affineOpens) :
    (GradedMonoid.GOne.one : (reesSituation I).sectionPieces U.1 0) =
      (reesSituation I).algebra.one.eval (op U.1) :=
  (Situation.sectionRingStructure (reesSituation I)).one_homogeneous U.1

/-- Restriction of a homogeneous section is restriction in its homogeneous piece. -/
public theorem sectionRingRestrict_of (U V : X.affineOpens) (h : U.1 ≤ V.1) (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    (reesSituation I).sectionRingRestrict U.1 V.1 h
        (DirectSum.of ((reesSituation I).sectionPieces V.1) n a) =
      DirectSum.of ((reesSituation I).sectionPieces U.1) n
        (((reesSituation I).algebra.piece (n : ℤ)).val.map (homOfLE h).op a) :=
  (Situation.sectionRingStructure (reesSituation I)).restrict_of U.1 V.1 h n a

/-- The canonical map from the structure sheaf multiplies the unit section. -/
public theorem sectionRingBaseMap_eq (U : X.affineOpens) (r : X.ringCatSheaf.obj.obj (op U.1)) :
    (reesSituation I).sectionRingBaseMap U.1 r =
      DirectSum.of ((reesSituation I).sectionPieces U.1) 0
        (r • (reesSituation I).algebra.one.eval (op U.1)) :=
  (Situation.sectionRingStructure (reesSituation I)).baseMap_apply U.1 r

/-! ### The comparison of graded rings over an affine open -/

/-- **The two gradings agree degreewise.** The degree-`n` homogeneous sections of the Rees algebra
sheaf over an affine open `U` are the degree-`n` part of the ordinary Rees algebra
`Γ(X, U)[I(U)t]`, both being `I(U)ⁿ`. -/
public def reesGradedPieceEquiv (U : X.affineOpens) (n : ℕ) :
    (reesSituation I).sectionPieces U.1 n ≃+ ↥(reesGrading (I.ideal U) n) :=
  (reesPieceEquiv I U n).trans (reesGradingEquivPow (I.ideal U) n).toAddEquiv

/-- A homogeneous section of degree `n` corresponds to the monomial of degree `n` with its
coefficient. -/
public theorem coe_reesGradedPieceEquiv (U : X.affineOpens) (n : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) :
    (((reesGradedPieceEquiv I U n a : ↥(reesGrading (I.ideal U) n)) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.monomial n (reesPieceEquiv I U n a : Γ(X, U.1)) :=
  coe_reesGradingEquivPow (I.ideal U) _

/-- The degree-`n` summand of the section ring, mapped into the ordinary Rees algebra. -/
public def reesToPieceHom (U : X.affineOpens) (n : ℕ) :
    (reesSituation I).sectionPieces U.1 n →+ ↥(reesAlgebra (I.ideal U)) where
  toFun a :=
    ((reesGradedPieceEquiv I U n a : ↥(reesGrading (I.ideal U) n)) : ↥(reesAlgebra (I.ideal U)))
  map_zero' := by simp
  map_add' a b := by simp

/-- The comparison map out of the graded section ring, as an additive homomorphism. -/
public def reesSectionToAddHom (U : X.affineOpens) :
    (reesSituation I).sectionRing U.1 →+ ↥(reesAlgebra (I.ideal U)) :=
  DirectSum.toAddMonoid (reesToPieceHom I U)

/-- The comparison map on a homogeneous section. -/
public theorem reesSectionToAddHom_of (U : X.affineOpens) (n : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) :
    reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n a) =
      ((reesGradedPieceEquiv I U n a : ↥(reesGrading (I.ideal U) n)) :
        ↥(reesAlgebra (I.ideal U))) :=
  DirectSum.toAddMonoid_of (reesToPieceHom I U) n a

/-- The comparison map on a homogeneous section, read as a polynomial. -/
public theorem coe_reesSectionToAddHom_of (U : X.affineOpens) (n : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) :
    ((reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n a) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.monomial n (reesPieceEquiv I U n a : Γ(X, U.1)) := by
  rw [reesSectionToAddHom_of, coe_reesGradedPieceEquiv]

/-- The degree-`n` part of the ordinary Rees algebra, mapped into the graded section ring. -/
public def reesFromPieceHom (U : X.affineOpens) (n : ℕ) :
    ↥(reesGrading (I.ideal U) n) →+ (reesSituation I).sectionRing U.1 :=
  (DirectSum.of ((reesSituation I).sectionPieces U.1) n).comp
    (reesGradedPieceEquiv I U n).symm.toAddMonoidHom

/-- The inverse comparison map, as an additive homomorphism: decompose into homogeneous parts and
apply the degreewise inverses. -/
public def reesSectionFromAddHom (U : X.affineOpens) :
    ↥(reesAlgebra (I.ideal U)) →+ (reesSituation I).sectionRing U.1 :=
  (DirectSum.toAddMonoid (reesFromPieceHom I U)).comp
    (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).toAddMonoidHom

/-- The inverse comparison map undoes the comparison map. -/
public theorem reesSectionFromAddHom_comp_toAddHom (U : X.affineOpens) :
    (reesSectionFromAddHom I U).comp (reesSectionToAddHom I U) = AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun n a ↦ ?_
  rw [AddMonoidHom.comp_apply, reesSectionToAddHom_of, AddMonoidHom.id_apply]
  show DirectSum.toAddMonoid (reesFromPieceHom I U)
    (DirectSum.decompose (reesGrading (I.ideal U))
      ((reesGradedPieceEquiv I U n a : ↥(reesGrading (I.ideal U) n)) :
        ↥(reesAlgebra (I.ideal U)))) = _
  rw [DirectSum.decompose_coe, DirectSum.toAddMonoid_of]
  show DirectSum.of ((reesSituation I).sectionPieces U.1) n
    ((reesGradedPieceEquiv I U n).symm (reesGradedPieceEquiv I U n a)) = _
  rw [AddEquiv.symm_apply_apply]

/-- The comparison map undoes the inverse comparison map. -/
public theorem reesSectionToAddHom_comp_fromAddHom (U : X.affineOpens) :
    (reesSectionToAddHom I U).comp (reesSectionFromAddHom I U) = AddMonoidHom.id _ := by
  have key : (reesSectionToAddHom I U).comp (DirectSum.toAddMonoid (reesFromPieceHom I U)) =
      (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).symm.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun n y ↦ ?_
    rw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
    show reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n
      ((reesGradedPieceEquiv I U n).symm y)) = _
    refine Eq.trans ?_ (DirectSum.decompose_symm_of (reesGrading (I.ideal U)) y).symm
    rw [reesSectionToAddHom_of, AddEquiv.apply_symm_apply]
  have hassoc : (reesSectionToAddHom I U).comp (reesSectionFromAddHom I U) =
      ((reesSectionToAddHom I U).comp (DirectSum.toAddMonoid (reesFromPieceHom I U))).comp
        (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).toAddMonoidHom :=
    (AddMonoidHom.comp_assoc (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).toAddMonoidHom
      (DirectSum.toAddMonoid (reesFromPieceHom I U)) (reesSectionToAddHom I U)).symm
  refine hassoc.trans (Eq.trans (congrArg (fun k : (_ →+ ↥(reesAlgebra (I.ideal U))) ↦
    k.comp (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).toAddMonoidHom) key) ?_)
  exact AddMonoidHom.ext fun f ↦
    (DirectSum.decomposeAddEquiv (reesGrading (I.ideal U))).symm_apply_apply f

/-- **The comparison map is multiplicative.** On homogeneous sections it is the identity
`monomial n r * monomial m s = monomial (n + m) (r * s)`, the coefficients matching by
`AlgebraicGeometry.coe_reesPieceEquiv_mul`. -/
public theorem reesSectionToAddHom_map_mul (U : X.affineOpens) :
    ∀ x y : (reesSituation I).sectionRing U.1, reesSectionToAddHom I U (x * y) =
      reesSectionToAddHom I U x * reesSectionToAddHom I U y := by
  rw [(reesSectionToAddHom I U).map_mul_iff]
  refine DirectSum.addHom_ext' fun n ↦ AddMonoidHom.ext fun a ↦ ?_
  refine DirectSum.addHom_ext' fun m ↦ AddMonoidHom.ext fun b ↦ ?_
  show reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n a *
      DirectSum.of ((reesSituation I).sectionPieces U.1) m b) =
    reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n a) *
      reesSectionToAddHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) m b)
  refine Subtype.ext ?_
  rw [Subalgebra.coe_mul, DirectSum.of_mul_of, gradedMul_eq, coe_reesSectionToAddHom_of,
    coe_reesSectionToAddHom_of, coe_reesSectionToAddHom_of, coe_reesPieceEquiv_mul,
    Polynomial.monomial_mul_monomial]

/-- **The graded ring of homogeneous local sections of the Rees algebra sheaf over an affine open
is the ordinary Rees algebra of the ideal there.** -/
public def reesSectionRingEquiv (U : X.affineOpens) :
    (reesSituation I).sectionRing U.1 ≃+* ↥(reesAlgebra (I.ideal U)) where
  toFun := reesSectionToAddHom I U
  invFun := reesSectionFromAddHom I U
  left_inv x := DFunLike.congr_fun (reesSectionFromAddHom_comp_toAddHom I U) x
  right_inv f := DFunLike.congr_fun (reesSectionToAddHom_comp_fromAddHom I U) f
  map_add' := (reesSectionToAddHom I U).map_add
  map_mul' := reesSectionToAddHom_map_mul I U

/-- The comparison isomorphism is the comparison map. -/
public theorem reesSectionRingEquiv_apply (U : X.affineOpens)
    (x : (reesSituation I).sectionRing U.1) :
    reesSectionRingEquiv I U x = reesSectionToAddHom I U x := rfl

/-- The inverse of the comparison isomorphism is the inverse comparison map. -/
public theorem reesSectionRingEquiv_symm_apply (U : X.affineOpens)
    (y : ↥(reesAlgebra (I.ideal U))) :
    (reesSectionRingEquiv I U).symm y = reesSectionFromAddHom I U y := rfl

/-- The comparison map preserves degrees. -/
public theorem reesSectionToAddHom_mem (U : X.affineOpens) (n : ℕ)
    {x : (reesSituation I).sectionRing U.1}
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 n) :
    reesSectionToAddHom I U x ∈ reesGrading (I.ideal U) n := by
  obtain ⟨a, rfl⟩ := hx
  rw [reesSectionToAddHom_of]
  exact (reesGradedPieceEquiv I U n a).2

/-- The inverse comparison map preserves degrees. -/
public theorem reesSectionFromAddHom_mem (U : X.affineOpens) (n : ℕ)
    {y : ↥(reesAlgebra (I.ideal U))} (hy : y ∈ reesGrading (I.ideal U) n) :
    reesSectionFromAddHom I U y ∈ (reesSituation I).sectionRingGrading U.1 n := by
  show DirectSum.toAddMonoid (reesFromPieceHom I U)
    (DirectSum.decompose (reesGrading (I.ideal U)) y) ∈
      (reesSituation I).sectionRingGrading U.1 n
  rw [DirectSum.decompose_of_mem _ hy, DirectSum.toAddMonoid_of]
  exact ⟨_, rfl⟩

/-- **The comparison isomorphism, as a homomorphism of graded rings.** -/
public def reesSectionGradedHom (U : X.affineOpens) :
    (reesSituation I).sectionRingGrading U.1 →+*ᵍ reesGrading (I.ideal U) where
  toRingHom := (reesSectionRingEquiv I U).toRingHom
  map_mem hx := reesSectionToAddHom_mem I U _ hx

/-- **The inverse comparison isomorphism, as a homomorphism of graded rings.** -/
public def reesSectionGradedHomInv (U : X.affineOpens) :
    reesGrading (I.ideal U) →+*ᵍ (reesSituation I).sectionRingGrading U.1 where
  toRingHom := (reesSectionRingEquiv I U).symm.toRingHom
  map_mem hy := reesSectionFromAddHom_mem I U _ hy

/-- The comparison homomorphism is the comparison map. -/
public theorem reesSectionGradedHom_apply (U : X.affineOpens)
    (x : (reesSituation I).sectionRing U.1) :
    reesSectionGradedHom I U x = reesSectionToAddHom I U x := rfl

/-- The comparison homomorphism applied to a homogeneous section, read as a polynomial. -/
public theorem coe_reesSectionGradedHom_of (U : X.affineOpens) (n : ℕ)
    (a : (reesSituation I).sectionPieces U.1 n) :
    ((reesSectionGradedHom I U (DirectSum.of ((reesSituation I).sectionPieces U.1) n a) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.monomial n (reesPieceEquiv I U n a : Γ(X, U.1)) := by
  rw [reesSectionGradedHom_apply, coe_reesSectionToAddHom_of]

/-! ### Naturality and the degree-zero identifications -/

/-- The comparison homomorphism applied to the restriction of a homogeneous section: the
coefficient restricts. -/
public theorem coe_reesSectionGradedHom_restrict_of {U V : X.affineOpens} (h : U.1 ≤ V.1) (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    ((reesSectionGradedHom I U ((reesSituation I).sectionRingRestrict U.1 V.1 h
          (DirectSum.of ((reesSituation I).sectionPieces V.1) n a)) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.monomial n
        (X.presheaf.map (homOfLE h).op (reesPieceEquiv I V n a : Γ(X, V.1))) :=
  (congrArg (fun z ↦ ((reesSectionGradedHom I U z : ↥(reesAlgebra (I.ideal U))) :
      Polynomial Γ(X, U.1))) (sectionRingRestrict_of I U V h n a)).trans
    ((coe_reesSectionGradedHom_of I U n
        (((reesSituation I).algebra.piece (n : ℤ)).val.map (homOfLE h).op a)).trans
      (congrArg (Polynomial.monomial n) (coe_reesPieceEquiv_restrict I U V h n a)))

/-- The restriction of the Rees algebras applied to the comparison of a homogeneous section: the
coefficient restricts. -/
public theorem coe_reesRestrict_reesSectionGradedHom_of {U V : X.affineOpens} (h : U ≤ V) (n : ℕ)
    (a : (reesSituation I).sectionPieces V.1 n) :
    ((reesRestrict I h (reesSectionGradedHom I V
          (DirectSum.of ((reesSituation I).sectionPieces V.1) n a)) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.monomial n ((sheafRestrict h).hom (reesPieceEquiv I V n a : Γ(X, V.1))) := by
  rw [coe_reesRestrict, coe_reesSectionGradedHom_of, Polynomial.map_monomial]

/-- **The comparison is natural in the affine open.** Both composites send a homogeneous section
of degree `n` over `V` to the degree-`n` monomial whose coefficient is its restriction to `U`. -/
public theorem reesSectionGradedHom_comp_gradedSectionRestriction {U V : X.affineOpens}
    (h : U ≤ V) :
    (reesSectionGradedHom I U).comp
        (Situation.gradedSectionRestriction (reesSituation I) U.1 V.1 h) =
      (reesRestrict I h).comp (reesSectionGradedHom I V) := by
  refine GradedRingHom.ext fun x ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n a =>
    exact Subtype.ext ((coe_reesSectionGradedHom_restrict_of I h n a).trans
      (coe_reesRestrict_reesSectionGradedHom_of I h n a).symm)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The degree-zero identification of the graded section ring, read inside the section ring. -/
public theorem coe_sectionRingZeroMap (U : X.affineOpens) (r : Γ(X, U.1)) :
    (((Situation.sectionRingZeroMap (reesSituation I) U.1).hom r :
        ↥((reesSituation I).sectionRingGrading U.1 0)) : (reesSituation I).sectionRing U.1) =
      (reesSituation I).sectionRingBaseMap U.1 r := by
  show ((GradedRing.projZeroRingHom' ((reesSituation I).sectionRingGrading U.1)
    ((reesSituation I).sectionRingBaseMap U.1 r) : (reesSituation I).sectionRing U.1)) = _
  rw [GradedRing.projZeroRingHom'_apply_coe _
    (⟨(reesSituation I).sectionRingBaseMap U.1 r,
      Situation.sectionRingBaseMap_mem_zero (reesSituation I) U.1 r⟩ :
        (reesSituation I).sectionRingGrading U.1 0)]

/-- The comparison homomorphism sends the image of a section of the structure sheaf to the
corresponding constant polynomial. -/
public theorem coe_reesSectionGradedHom_baseMap (U : X.affineOpens)
    (r : X.ringCatSheaf.obj.obj (op U.1)) :
    ((reesSectionGradedHom I U ((reesSituation I).sectionRingBaseMap U.1 r) :
        ↥(reesAlgebra (I.ideal U))) : Polynomial Γ(X, U.1)) =
      Polynomial.C (show Γ(X, U.1) from r) := by
  rw [sectionRingBaseMap_eq, coe_reesSectionGradedHom_of, coe_reesPieceEquiv_smul,
    coe_reesPieceEquiv_one, mul_one, Polynomial.monomial_zero_left]

/-- **The comparison is compatible with the two degree-zero identifications with `Γ(X, U)`.**
Both composites send a section `r` over `U` to the constant polynomial `C r`. -/
public theorem sectionRingZeroMap_comp_reesSectionGradedHom (U : X.affineOpens) :
    Situation.sectionRingZeroMap (reesSituation I) U.1 ≫
        CommRingCat.ofHom (reesSectionGradedHom I U).gradedZeroRingHom =
      reesBase I U := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext (Subtype.ext ?_))
  exact ((congrArg (fun z ↦ ((reesSectionGradedHom I U z : ↥(reesAlgebra (I.ideal U))) :
      Polynomial Γ(X, U.1))) (coe_sectionRingZeroMap I U r)).trans
    (coe_reesSectionGradedHom_baseMap I U r)).trans (coe_reesBase_apply I U r).symm

/-! ### The two blowups agree -/

/-- **The two relative-`Proj` gluing data of the Rees algebra of `I` are isomorphic.** The graded
ring over an affine open `U` is the graded ring of homogeneous sections of the Rees algebra sheaf
on one side and the ordinary Rees algebra `Γ(X, U)[I(U)t]` on the other, and
`AlgebraicGeometry.reesSectionGradedHom` identifies them compatibly with restriction and with the
degree-zero identifications. -/
public def reesDataIso :
    Data.Iso (Situation.chartData (reesSituation I)) (reesData I) where
  hom U := reesSectionGradedHom I U
  inv U := reesSectionGradedHomInv I U
  inv_comp_hom U := GradedRingHom.ext fun x ↦ (reesSectionRingEquiv I U).symm_apply_apply x
  hom_comp_inv U := GradedRingHom.ext fun y ↦ (reesSectionRingEquiv I U).apply_symm_apply y
  hom_comp_restrict h := reesSectionGradedHom_comp_gradedSectionRestriction I h
  base_comp_hom U := sectionRingZeroMap_comp_reesSectionGradedHom I U

/-- **The two blowups of `X` in `I` agree.** The blowup built as the relative `Proj` of the Rees
algebra *sheaf* and the blowup built by gluing the `Proj` of the ordinary Rees algebras
`Γ(X, U)[I(U)t]` are canonically isomorphic. The isomorphism is over `X`:
see `AlgebraicGeometry.blowUpIso_hom_blowUpToBase`. -/
public def blowUpIso : blowUp I ≅ Stacks.Blowup.blowUp I := (reesDataIso I).relativeProjIso

/-- **The comparison isomorphism of blowups is an isomorphism over `X`**: it commutes with the two
blowup morphisms. This is what identifies the two constructions as the same blowup of `X` in `I`;
a bare isomorphism of schemes would not. -/
public theorem blowUpIso_hom_blowUpToBase :
    (blowUpIso I).hom ≫ Stacks.Blowup.blowUpToBase I = blowUpToBase I :=
  (reesDataIso I).relativeProjIso_hom_toBase

/-- The comparison isomorphism of blowups is compatible with the affine charts: over an affine
open `U` of the base it is the comparison of the two charts, `Proj` of the two graded rings. -/
public theorem relativeProjChart_blowUpIso_hom (U : X.affineOpens) :
    (reesSituation I).relativeProjChart U ≫ (blowUpIso I).hom =
      ((reesDataIso I).projIso U).hom ≫ blowUpChart I U :=
  (reesDataIso I).chartι_relativeProjIso_hom U

end AlgebraicGeometry

end
