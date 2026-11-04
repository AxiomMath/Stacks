module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.FreeChart
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation

/-!
# The section ring of the projective bundle situation of `𝒪_X^{n+1}` is a polynomial ring

The projective bundle of a quasi-coherent `𝒪_X`-module `E` is the relative `Proj` of
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E`, whose graded ring of homogeneous
local sections over an open `U` is `⨁_{k ≥ 0} Γ(Sym^k(E), U)`. **For `E = 𝒪_X^{n+1}` this file
identifies that ring, as a graded ring, with the polynomial ring `Γ(X, U)[T₀, …, Tₙ]` graded by
total degree.**

`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.FreeChart` proves the same statement for the
other relative-`Proj` substrate, `SheafGradedAlgebra`. The two section rings have the same
carrier and the same grading — by `rfl` — but not the same `CommRing` instance: the
`SheafGradedAlgebra` one is read off `DirectSum.of_mul_of`, while the `Situation` one is selected
by `Classical.choice` from `Stacks.RelativeProj.Situation.sectionRingStructure_exists`. So the
comparison has to be rebuilt here, against the chosen structure's defining equations; only the
degreewise comparison `Stacks.SymGraded.chartPieceEquiv` is shared.

## Main definitions

* `Stacks.SymGraded.freeSituation`: the projective bundle situation of `𝒪_X^{n+1}`.
* `Stacks.SymGraded.freeSituationPieceRingEquiv`: the degreewise comparisons, assembled into a
  ring isomorphism of the direct sums.
* `Stacks.SymGraded.freeSituationSectionsRingEquiv`:
  **`Γ(X, U)[T₀, …, Tₙ] ≃+* (freeSituation X n).sectionRing U`.**
* `Stacks.SymGraded.freeSituationGradedHom` and `Stacks.SymGraded.freeSituationGradedInv`: that
  isomorphism and its inverse as homomorphisms of graded rings.

## Main results

* `Stacks.SymGraded.freeSituationGradedMul` and `Stacks.SymGraded.freeSituationGradedOne`:
  multiplication and the unit in the chosen section-ring structure are those of the graded
  algebra, on homogeneous sections.
* `Stacks.SymGraded.freeSituationSectionsRingEquiv_C`: **the comparison carries a constant to the
  canonical map from the structure sheaf**, so it is an isomorphism of `Γ(X, U)`-algebras and not
  merely of graded rings.
* `Stacks.SymGraded.freeSituationSectionsRingEquiv_X_restrict`: **the homogeneous coordinates
  `Tⱼ` are natural in the open.**

## Implementation notes

**One bridging instance.** `Stacks.RelativeProj.Situation.sectionRingGradedRing` is indexed by
`U : s.base.Opens`. For `s = freeSituation X n` that type is `X.Opens` definitionally, but
`(freeSituation X n).base` is a chain of plain `def`s, which instance search does not unfold, so
`Semiring ((freeSituation X n).sectionRing U)` is not synthesizable for `U : X.Opens`.
`Stacks.SymGraded.freeSituationGCommRing` is that instance with `U : X.Opens`; its body is the
same term, so no transport is involved anywhere below.

**Where the grading is taken.** As in
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.FreeChart`, the source grading is
`MvPolynomial.homogeneousSubmodule` and never `SymPow.symmetricPower`: the latter makes
`DirectSum.gradedCongrRingEquiv` unfold a `RingCon` quotient of a tensor algebra and the
unification does not terminate. The two type families of that application are also passed
explicitly, without which the elaborator spends the whole heartbeat budget in `whnf`.

**Why the multiplicativity proof is not a `rewrite`.** The chosen structure's equation for
homogeneous multiplication is an `HEq`, and the correction from it to the graded multiplication of
the direct sum is applied by `Eq.trans` rather than by rewriting: a motive mentioning
`(freeSituation X n).base.ringCatSheaf`, which the sections of a homogeneous piece do mention,
does not typecheck at `instance` transparency even though it is `X.ringCatSheaf` definitionally.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (n : ℕ)

/-! ### The situation, and its section-ring structure on an open -/

/-- **The projective bundle situation of `𝒪_X^{n+1}`**: the relative `Proj` situation of the
symmetric algebra of the free module sheaf on `n + 1` generators. -/
def freeSituation (X : Scheme.{u}) (n : ℕ) : RelativeProj.Situation.{u} :=
  RelativeProj.symmetricSituationOfQuasicoherent X (freeModule (X := X) (coordIndex n))

/-- The base scheme of `freeSituation X n` is `X`. -/
theorem freeSituation_base : (freeSituation X n).base = X := rfl

/-- The graded algebra of `freeSituation X n` is the symmetric algebra of the free module sheaf
on `n + 1` generators. -/
theorem freeSituation_algebra :
    (freeSituation X n).algebra =
      Scheme.Modules.symmetricAlgebra X (freeModule (X := X) (coordIndex n)) := rfl

/-- The graded-ring structure on the homogeneous sections over an open, indexed by `X.Opens`.
This is `Stacks.RelativeProj.Situation.sectionRingGradedRing` verbatim; see the implementation
notes for why the restatement is needed. -/
instance freeSituationGCommRing (U : X.Opens) :
    DirectSum.GCommRing ((freeSituation X n).sectionPieces U) :=
  RelativeProj.Situation.sectionRingGradedRing (freeSituation X n) U

/-- Multiplication of homogeneous sections in the section ring is multiplication in the graded
algebra. -/
theorem freeSituationGradedMul (U : X.Opens) (i j : ℕ)
    (a : (freeSituation X n).sectionPieces U i) (b : (freeSituation X n).sectionPieces U j) :
    (GradedMonoid.GMul.mul a b : (freeSituation X n).sectionPieces U (i + j)) =
      ((freeSituation X n).algebra.mul (i : ℤ) (j : ℤ)).app (op U) a b :=
  eq_of_heq
    ((RelativeProj.Situation.sectionRingStructure (freeSituation X n)).mul_homogeneous U i j a b)

/-- The unit of the section ring is the unit section of the graded algebra. -/
theorem freeSituationGradedOne (U : X.Opens) :
    (GradedMonoid.GOne.one : (freeSituation X n).sectionPieces U 0) =
      (freeSituation X n).algebra.one.eval (op U) :=
  (RelativeProj.Situation.sectionRingStructure (freeSituation X n)).one_homogeneous U

/-- Restriction of a homogeneous section is restriction in its homogeneous piece. -/
theorem freeSituationRestrict_of {U V : X.Opens} (h : U ≤ V) (k : ℕ)
    (a : (freeSituation X n).sectionPieces V k) :
    (freeSituation X n).sectionRingRestrict U V h
        (DirectSum.of ((freeSituation X n).sectionPieces V) k a) =
      DirectSum.of ((freeSituation X n).sectionPieces U) k
        (((freeSituation X n).algebra.piece (k : ℤ)).val.map (homOfLE h).op a) :=
  (RelativeProj.Situation.sectionRingStructure (freeSituation X n)).restrict_of U V h k a

/-- The canonical map from the structure sheaf multiplies the unit section. -/
theorem freeSituationBaseMap_eq (U : X.Opens)
    (r : (freeSituation X n).base.ringCatSheaf.obj.obj (op U)) :
    (freeSituation X n).sectionRingBaseMap U r =
      DirectSum.of ((freeSituation X n).sectionPieces U) 0
        (r • (freeSituation X n).algebra.one.eval (op U)) :=
  (RelativeProj.Situation.sectionRingStructure (freeSituation X n)).baseMap_apply U r

/-! ### The comparison with a polynomial ring -/

/-- The degreewise comparisons, assembled into a ring isomorphism of the direct sums. -/
def freeSituationPieceRingEquiv (U : X.Opens) :
    (⨁ k : ℕ, ↥(MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k)) ≃+*
      (freeSituation X n).sectionRing U :=
  DirectSum.gradedCongrRingEquiv
    (A := fun k : ℕ => ↥(MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k))
    (B := fun k : ℕ => (freeSituation X n).sectionPieces U k)
    (fun k : ℕ => chartPieceEquiv n U k)
    (fun i j x y => by
      refine Eq.trans ?_ (freeSituationGradedMul n U i j
        (chartPieceEquiv n U i x) (chartPieceEquiv n U j y)).symm
      refine Eq.trans (congrArg (freePieceEquiv (coordIndex n) (i + j) (op U)) ?_)
        (freePieceEquiv_mul (coordIndex n) i j (op U) _ _)
      refine Subtype.ext ?_
      rw [coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv]
      change _ = _ * _
      rw [coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv,
        coe_symmetricPowerEquivHomogeneousSubmodule_symm_toEquiv, SetLike.coe_gMul, map_mul]
      rfl)

/-- `freeSituationPieceRingEquiv` on a homogeneous element is the degreewise comparison
`chartPieceEquiv`, placed in its degree. -/
theorem freeSituationPieceRingEquiv_of (U : X.Opens) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    freeSituationPieceRingEquiv n U (DirectSum.of _ k z) =
      DirectSum.of ((freeSituation X n).sectionPieces U) k (chartPieceEquiv n U k z) :=
  DirectSum.gradedCongr_of
    (A := fun k : ℕ => ↥(MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k))
    (B := fun k : ℕ => (freeSituation X n).sectionPieces U k)
    (fun k : ℕ => chartPieceEquiv n U k) k z

/-- **The graded ring of homogeneous local sections of the projective bundle situation of
`𝒪_X^{n+1}` over an open is the polynomial ring in `n + 1` variables over the sections of the
structure sheaf.** -/
def freeSituationSectionsRingEquiv (U : X.Opens) :
    MvPolynomial (coordIndex n) ↥(siteRing X (op U)) ≃+*
      (freeSituation X n).sectionRing U :=
  (DirectSum.decomposeRingEquiv
      (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)))).trans
    (freeSituationPieceRingEquiv n U)

/-- `freeSituationSectionsRingEquiv` is `freeSituationPieceRingEquiv` applied to the decomposition
of a polynomial into its homogeneous components. -/
theorem freeSituationSectionsRingEquiv_apply (U : X.Opens)
    (x : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) :
    freeSituationSectionsRingEquiv n U x =
      freeSituationPieceRingEquiv n U
        (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) x) :=
  rfl

/-- The comparison on a homogeneous polynomial is the degreewise comparison, placed in its
degree. -/
theorem freeSituationSectionsRingEquiv_coe (U : X.Opens) (k : ℕ)
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    freeSituationSectionsRingEquiv n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      DirectSum.of ((freeSituation X n).sectionPieces U) k (chartPieceEquiv n U k z) := by
  rw [freeSituationSectionsRingEquiv_apply,
    DirectSum.decompose_coe
      (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) z,
    freeSituationPieceRingEquiv_of]

/-- The comparison sends a homogeneous polynomial to `y` in its degree, if the degreewise
comparison sends it to `y`. -/
private theorem freeSituationSectionsRingEquiv_coe_of_eq (U : X.Opens) {k : ℕ}
    (z : MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k)
    {y : (freeSituation X n).sectionPieces U k} (h : chartPieceEquiv n U k z = y) :
    freeSituationSectionsRingEquiv n U (z : MvPolynomial (coordIndex n) ↥(siteRing X (op U))) =
      DirectSum.of ((freeSituation X n).sectionPieces U) k y :=
  h ▸ freeSituationSectionsRingEquiv_coe n U k z

/-! ### Compatibility with the gradings -/

/-- The comparison carries the degree-`k` homogeneous polynomials into the degree-`k` part of the
section ring. -/
theorem freeSituationSectionsRingEquiv_mem_grading (U : X.Opens) {k : ℕ}
    {x : MvPolynomial (coordIndex n) ↥(siteRing X (op U))}
    (hx : x ∈ MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k) :
    freeSituationSectionsRingEquiv n U x ∈ (freeSituation X n).sectionRingGrading U k := by
  rw [freeSituationSectionsRingEquiv_apply, DirectSum.decompose_of_mem _ hx,
    freeSituationPieceRingEquiv_of]
  exact ⟨_, rfl⟩

/-- The inverse comparison carries the degree-`k` part of the section ring into the degree-`k`
homogeneous polynomials. -/
theorem freeSituationSectionsRingEquiv_symm_mem (U : X.Opens) {k : ℕ}
    {z : (freeSituation X n).sectionRing U}
    (hz : z ∈ (freeSituation X n).sectionRingGrading U k) :
    (freeSituationSectionsRingEquiv n U).symm z ∈
      MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) k := by
  obtain ⟨y, rfl⟩ := hz
  rw [← freeSituationSectionsRingEquiv_coe_of_eq n U _
    ((chartPieceEquiv n U k).apply_symm_apply y),
    (freeSituationSectionsRingEquiv n U).symm_apply_apply]
  exact ((chartPieceEquiv n U k).symm y).2

/-- **The comparison as a homomorphism of graded rings.** -/
def freeSituationGradedHom (U : X.Opens) :
    MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) →+*ᵍ
      (freeSituation X n).sectionRingGrading U where
  toRingHom := (freeSituationSectionsRingEquiv n U).toRingHom
  map_mem hx := freeSituationSectionsRingEquiv_mem_grading n U hx

/-- **The inverse comparison as a homomorphism of graded rings.** -/
def freeSituationGradedInv (U : X.Opens) :
    (freeSituation X n).sectionRingGrading U →+*ᵍ
      MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U)) where
  toRingHom := (freeSituationSectionsRingEquiv n U).symm.toRingHom
  map_mem hz := freeSituationSectionsRingEquiv_symm_mem n U hz

/-- `freeSituationGradedHom` composed with `freeSituationGradedInv` is the identity. -/
theorem freeSituationGradedHom_comp_inv (U : X.Opens) :
    (freeSituationGradedHom n U).comp (freeSituationGradedInv n U) =
      GradedRingHom.id ((freeSituation X n).sectionRingGrading U) :=
  GradedRingHom.ext fun z => (freeSituationSectionsRingEquiv n U).apply_symm_apply z

/-- `freeSituationGradedInv` composed with `freeSituationGradedHom` is the identity. -/
theorem freeSituationGradedInv_comp_hom (U : X.Opens) :
    (freeSituationGradedInv n U).comp (freeSituationGradedHom n U) =
      GradedRingHom.id
        (MvPolynomial.homogeneousSubmodule (coordIndex n) ↥(siteRing X (op U))) :=
  GradedRingHom.ext fun x => (freeSituationSectionsRingEquiv n U).symm_apply_apply x

/-! ### The degree-zero part, and naturality in the open -/

/-- **The degree-`0` half of the comparison: it is the canonical map from the structure sheaf.**
The comparison carries the constant polynomial `C r` to
`Stacks.RelativeProj.Situation.sectionRingBaseMap` of `r`, so it is an isomorphism of
`Γ(X, U)`-algebras and not merely of graded rings. -/
theorem freeSituationSectionsRingEquiv_C (U : X.Opens) (r : ↥(siteRing X (op U))) :
    freeSituationSectionsRingEquiv n U (MvPolynomial.C r) =
      (freeSituation X n).sectionRingBaseMap U r :=
  (freeSituationSectionsRingEquiv_coe_of_eq n U
      ⟨MvPolynomial.C r,
        MvPolynomial.C_mem_homogeneousSubmodule_zero (coordIndex n) ↥(siteRing X (op U)) r⟩
      (chartPieceEquiv_zero_C n U r)).trans (freeSituationBaseMap_eq n U r).symm

/-- **The homogeneous coordinates are natural in the open.** Restriction of homogeneous sections
carries the section `Tⱼ` over `V` to the section `Tⱼ` over `U`.

The integral polynomial ring is generated over `ℤ` by its variables, so this is the whole
naturality content a comparison out of the section rings needs. -/
theorem freeSituationSectionsRingEquiv_X_restrict {U V : X.Opens} (h : U ≤ V)
    (j : coordIndex n) :
    (freeSituation X n).sectionRingRestrict U V h
        (freeSituationSectionsRingEquiv n V (MvPolynomial.X j)) =
      freeSituationSectionsRingEquiv n U (MvPolynomial.X j) := by
  have hj : (Finsupp.single j 1 : coordIndex n →₀ ℕ).degree = 1 := by simp
  have key : ∀ W : X.Opens,
      (MvPolynomial.basisHomogeneousSubmodule (coordIndex n) ↥(siteRing X (op W)) 1
        ⟨Finsupp.single j 1, hj⟩ : MvPolynomial (coordIndex n) ↥(siteRing X (op W))) =
        MvPolynomial.X j := fun W => by
    rw [MvPolynomial.coe_basisHomogeneousSubmodule_apply]
    simp [MvPolynomial.X]
  rw [← key V, ← key U, freeSituationSectionsRingEquiv_coe, freeSituationSectionsRingEquiv_coe]
  exact (freeSituationRestrict_of n h 1 _).trans
    (congrArg (DirectSum.of ((freeSituation X n).sectionPieces U) 1)
      (resPiece_chartPieceEquiv n 1 h ⟨Finsupp.single j 1, hj⟩))

end Stacks.SymGraded

end
