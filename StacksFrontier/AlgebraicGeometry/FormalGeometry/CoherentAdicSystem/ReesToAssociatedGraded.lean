module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOnBasis
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded

/-!
# The Rees algebra of an ideal sheaf surjects onto its associated graded algebra

For a quasi-coherent sheaf of ideals `ℐ` on a scheme `X` the Rees algebra `⨁_{n ≥ 0} ℐⁿ`
(`Stacks.Blowup.reesGradedAlgebra`) maps onto the associated graded algebra
`⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹`, degree by degree, by taking classes.

This file builds that homomorphism of sheaves of graded algebras, and transports graded modules
along it: a graded module over the associated graded algebra becomes a graded module over the
Rees algebra, with the same homogeneous pieces.

## The construction

`Stacks.Coherent.AssociatedGradedAlgebraData` identifies, over every affine open `U`, the
degree-`n` piece of the associated graded algebra with `Iᵁⁿ / Iᵁⁿ⁺¹`, compatibly with the
`Γ(X, U)`-module structure, the multiplication and restriction. The chart map sends a homogeneous
section of the Rees algebra to the class of its ambient section
(`Stacks.Blowup.reesPieceAmbient`), and
`Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis` glues the chart maps over the basis
of affine opens. On every affine chart the unit of the associated graded algebra is the class of
`1` (`Stacks.Coherent.algebraPiece_zero_one`), so the glued homomorphism is unital.

## Main definitions

* `Stacks.Coherent.reesToAssociatedGraded`: the homomorphism of sheaves of graded algebras
  `⨁ ℐⁿ ⟶ ⨁ ℐⁿ/ℐⁿ⁺¹`, as a `SheafOfModules.GradedAlgebra.UnitalHom`.
* `Stacks.Coherent.restrictGradedModule`: a graded module over the codomain of a unital
  homomorphism of sheaves of graded algebras, read as a graded module over the domain.
* `Stacks.Coherent.reesTransitionGradedModule`: the graded module `⨁ₙ Ker(F_{n+1} ⟶ F_n)` of
  [Stacks, Tag 087Z], read as a graded module over the Rees algebra.

## Main results

* `Stacks.Coherent.reesToAssociatedGradedHom_app_app`: over an affine open the homomorphism is
  the chart map, which takes the class of the ambient section.
* `Stacks.Coherent.exists_reesToAssociatedGraded_app_eq`: it is surjective on the sections over
  an affine open, in every nonnegative degree.
* `Stacks.Coherent.smul_piece_eq_zero_of_mem`: a section of `ℐ` annihilates every homogeneous
  section of a graded module over the associated graded algebra.

## References

* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Blowup

universe u

namespace Stacks.Coherent

attribute [local instance] moduleOfSections

variable {X : Scheme.{u}} {I : X.IdealSheafData} (D : AssociatedGradedAlgebraData I)

/-- Every section of a zero sheaf of modules is zero. -/
theorem sections_eq_zero_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M)
    (U : X.Opensᵒᵖ) (x : M.val.obj U) : x = 0 := by
  have hid := (IsZero.iff_id_eq_zero M).mp hM
  have happ := congrArg (fun f : M ⟶ M => f.val.app U x) hid
  rw [show ((𝟙 M : M ⟶ M).val.app U) = 𝟙 _ from rfl,
    show ((0 : M ⟶ M).val.app U) = 0 from rfl] at happ
  simpa using happ

/-! ### The chart maps -/

/-- The ambient section of a homogeneous section of the Rees algebra over an affine open, read
in the `n`-th step of the ideal-power filtration of `Γ(X, U)`. -/
def reesAmbientPower (U : X.affineOpens) (n : ℕ)
    (x : ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1)) :
    AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n :=
  ⟨reesPieceAmbient I (n : ℤ) U.1 x, by
    rw [AssociatedGraded.ring_power_eq]
    simpa using reesPieceAmbient_mem_affine I (n : ℤ) (Int.natCast_nonneg n) U x⟩

/-- Reading the ambient section, as a `Γ(X, U)`-linear map. -/
def reesAmbientPowerLin (U : X.affineOpens) (n : ℕ) :
    ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1) →ₗ[Γ(X, U.1)]
      AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n where
  toFun := reesAmbientPower U n
  map_add' x y := Subtype.ext (reesPieceAmbient_add I (n : ℤ) U.1 x y)
  map_smul' r x := Subtype.ext (reesPieceAmbient_smul I (n : ℤ) U.1 r x)

/-- The affine identification of a homogeneous piece of the associated graded algebra, as a
`Γ(X, U)`-linear equivalence: the datum's identification is additive and `Γ(X, U)`-linear. -/
def algebraPieceLinearEquiv (U : X.affineOpens) (n : ℕ) :
    (D.algebra.piece (n : ℤ)).val.obj (op U.1) ≃ₗ[Γ(X, U.1)]
      AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) n :=
  { D.algebraPiece n U with map_smul' := fun r a => D.algebraPiece_smul n U r a }

/-- `algebraPieceLinearEquiv` applies the datum's affine identification. -/
@[simp]
theorem algebraPieceLinearEquiv_apply (U : X.affineOpens) (n : ℕ)
    (a : (D.algebra.piece (n : ℤ)).val.obj (op U.1)) :
    algebraPieceLinearEquiv D U n a = D.algebraPiece n U a := rfl

/-- **The chart map in a nonnegative degree**: a homogeneous section of the Rees algebra over an
affine open goes to the class of its ambient section. -/
def reesChartMapNat (U : X.affineOpens) (n : ℕ) :
    ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1) →ₗ[Γ(X, U.1)]
      (D.algebra.piece (n : ℤ)).val.obj (op U.1) :=
  (algebraPieceLinearEquiv D U n).symm.toLinearMap ∘ₗ
    (((AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) (n + 1)).comap
      (AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) n).subtype).mkQ) ∘ₗ
    reesAmbientPowerLin U n

/-- The chart map sends a homogeneous section to the preimage, under the datum's affine
identification, of the class of its ambient section. -/
theorem reesChartMapNat_apply (U : X.affineOpens) (n : ℕ)
    (x : ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1)) :
    reesChartMapNat D U n x =
      (D.algebraPiece n U).symm
        (AssociatedGraded.mk (I.ideal U) n (reesAmbientPower U n x)) := rfl

/-- The chart identification undoes the chart map in a nonnegative degree: it returns the class
of the ambient section. -/
private theorem algebraPiece_reesChartMapNat (U : X.affineOpens) (n : ℕ)
    (x : ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1)) :
    D.algebraPiece n U (reesChartMapNat D U n x) =
      AssociatedGraded.mk (I.ideal U) n (reesAmbientPower U n x) := by
  rw [reesChartMapNat_apply, AddEquiv.apply_symm_apply]

/-! ### The unit of the associated graded algebra -/

/-- **The unit of the associated graded algebra is the class of `1` on every affine chart**:
the datum's degree-zero identification over an affine open `U` sends the unit section to the
class of `1` in `Iᵁ⁰ / Iᵁ¹`. -/
theorem algebraPiece_zero_one (U : X.affineOpens) :
    D.algebraPiece 0 U (D.algebra.one.eval (op U.1)) =
      AssociatedGraded.mk (I.ideal U) 0 ⟨1, by simp [AssociatedGraded.power]⟩ := by
  have hmem : (1 : Γ(X, U.1)) ∈ AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) 0 := by
    simp [AssociatedGraded.power]
  set o := D.algebra.one.eval (op U.1) with ho
  set a : (D.algebra.piece ((0 : ℕ) : ℤ)).val.obj (op U.1) :=
    (D.algebraPiece 0 U).symm (AssociatedGraded.mk (I.ideal U) 0 ⟨1, hmem⟩) with ha
  have hone : (D.algebra.mul ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ)).app (op U.1) o a = a :=
    eq_of_heq (D.algebra.one_mul ((0 : ℕ) : ℤ) (op U.1) a)
  have h2 : D.algebraPiece 0 U ((D.algebra.mul ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ)).app (op U.1) o a) =
      AssociatedGraded.homogeneousSMul (I.ideal U)
        (D.algebraPiece 0 U o) (D.algebraPiece 0 U a) :=
    eq_of_heq (D.algebraMul 0 0 U o a)
  rw [hone] at h2
  have hval : D.algebraPiece 0 U a = AssociatedGraded.mk (I.ideal U) 0 ⟨1, hmem⟩ := by
    rw [ha, AddEquiv.apply_symm_apply]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (D.algebraPiece 0 U o)
  have hz' : AssociatedGraded.mk (I.ideal U) 0 z = D.algebraPiece 0 U o := hz
  rw [hval, ← hz', AssociatedGraded.homogeneousSMul_mk] at h2
  rw [← hz']
  exact (congrArg (AssociatedGraded.mk (I.ideal U) 0) (Subtype.ext (by simp))).trans h2.symm

/-- **A section of `ℐ` annihilates every homogeneous section of a graded module over the
associated graded algebra**: over an affine open `U`, every `a ∈ Iᵁ` acts as zero on the
sections over `U` of every homogeneous piece. -/
theorem smul_piece_eq_zero_of_mem (N : SheafOfModules.GradedModule D.algebra)
    (U : X.affineOpens) {a : Γ(X, U.1)} (ha : a ∈ I.ideal U) (n : ℤ)
    (x : (N.piece n).val.obj (op U.1)) : a • x = 0 := by
  have hone : a • D.algebra.one.eval (op U.1) = 0 := by
    refine (D.algebraPiece 0 U).injective ?_
    have h1 := D.algebraPiece_smul 0 U a (D.algebra.one.eval (op U.1))
    have h2 : a • D.algebraPiece 0 U (D.algebra.one.eval (op U.1)) = 0 := by
      rw [algebraPiece_zero_one D U]
      exact AssociatedGraded.smul_eq_zero_of_mem (I.ideal U) 0 ha _
    exact (h1.trans h2).trans (map_zero (D.algebraPiece 0 U)).symm
  have key : ∀ m : ℤ, n + 0 = m → ∀ y : (N.piece m).val.obj (op U.1),
      HEq (N.smul n 0 (op U.1) x (D.algebra.one.eval (op U.1))) y → a • y = 0 := by
    rintro m rfl y hy
    have hy' : y = N.smul n 0 (op U.1) x (D.algebra.one.eval (op U.1)) := (eq_of_heq hy).symm
    subst hy'
    have h1 := N.smul_smul_right n 0 (op U.1) a x (D.algebra.one.eval (op U.1))
    have h2 : N.smul n 0 (op U.1) x (a • D.algebra.one.eval (op U.1)) =
        N.smul n 0 (op U.1) x 0 := congrArg _ hone
    exact (h1.symm.trans h2).trans (map_zero _)
  exact key n (add_zero n) x (N.smul_one n (op U.1) x)

/-! ### The chart maps in every degree, and the homomorphism they glue to -/

/-- The chart map in an arbitrary degree: the class of the ambient section in a nonnegative
degree, and zero in a negative degree, where the Rees algebra vanishes. -/
def reesChartMap (U : X.affineOpens) : (n : ℤ) →
    (((reesGradedAlgebra I).piece n).val.obj (op U.1) ⟶
      ((D.algebra).piece n).val.obj (op U.1))
  | .ofNat k => ModuleCat.ofHom (reesChartMapNat D U k)
  | .negSucc _ => 0

/-- In a nonnegative degree the chart map is `reesChartMapNat`. -/
theorem reesChartMap_ofNat_eq (U : X.affineOpens) (k : ℕ) :
    reesChartMap D U (k : ℤ) = ModuleCat.ofHom (reesChartMapNat D U k) := rfl

/-- In a nonnegative degree the chart map sends a homogeneous section to the preimage, under the
datum's affine identification, of the class of its ambient section. -/
theorem reesChartMap_ofNat (U : X.affineOpens) (k : ℕ)
    (x : ((reesGradedAlgebra I).piece (k : ℤ)).val.obj (op U.1)) :
    reesChartMap D U (k : ℤ) x =
      (D.algebraPiece k U).symm
        (AssociatedGraded.mk (I.ideal U) k (reesAmbientPower U k x)) := rfl

/-- In a negative degree the chart map is zero. -/
theorem reesChartMap_of_neg (U : X.affineOpens) {n : ℤ} (hn : n < 0) :
    reesChartMap D U n = 0 := by
  match n with
  | .ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | .negSucc k => rfl

/-- The chart identification undoes the chart map: it returns the class of the ambient
section. -/
theorem algebraPiece_reesChartMap (U : X.affineOpens) (n : ℕ)
    (x : ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1)) :
    D.algebraPiece n U (reesChartMap D U (n : ℤ) x) =
      AssociatedGraded.mk (I.ideal U) n (reesAmbientPower U n x) :=
  algebraPiece_reesChartMapNat D U n x

/-- The chart maps commute with the restriction maps between affine opens. -/
theorem reesChartMap_compatible (n : ℤ) :
    Stacks.BasisRestriction.IsCompatibleOnBasis ((reesGradedAlgebra I).piece n)
      (D.algebra.piece n) (fun V : X.affineOpens => V.1) (fun V => reesChartMap D V n) := by
  intro U V h s
  dsimp only
  by_cases hn : n < 0
  · exact (sections_eq_zero_of_isZero _ (D.algebraNegative n hn) _ _).trans
      (sections_eq_zero_of_isZero _ (D.algebraNegative n hn) _ _).symm
  lift n to ℕ using le_of_not_gt hn
  refine (D.algebraPiece n V).injective ?_
  refine (algebraPiece_reesChartMap D V n _).trans ?_
  refine Eq.trans ?_ (D.algebraPiece_naturality n U V h _).symm
  refine Eq.trans ?_ (congrArg (D.algebraRestriction n U V h)
    (algebraPiece_reesChartMap D U n s)).symm
  refine Eq.trans ?_ (D.algebraRestriction_mk n U V h (reesAmbientPower U n s)).symm
  refine congrArg (AssociatedGraded.mk (M := Γ(X, V.1)) (I.ideal V) n) (Subtype.ext ?_)
  exact reesPieceAmbient_restrict I (n : ℤ) V.1 U.1 h s

/-- The chart maps are multiplicative in a pair of nonnegative degrees. -/
theorem reesChartMapNat_mul (U : X.affineOpens) (k l : ℕ)
    (x : ((reesGradedAlgebra I).piece (k : ℤ)).val.obj (op U.1))
    (y : ((reesGradedAlgebra I).piece (l : ℤ)).val.obj (op U.1)) :
    reesChartMapNat D U (k + l)
        (((reesGradedAlgebra I).mul (k : ℤ) (l : ℤ)).app (op U.1) x y) =
      (D.algebra.mul (k : ℤ) (l : ℤ)).app (op U.1)
        (reesChartMapNat D U k x) (reesChartMapNat D U l y) := by
  refine (D.algebraPiece (k + l) U).injective ?_
  refine Eq.trans ?_ (eq_of_heq (D.algebraMul k l U
    (reesChartMapNat D U k x) (reesChartMapNat D U l y))).symm
  rw [algebraPiece_reesChartMapNat, algebraPiece_reesChartMapNat, algebraPiece_reesChartMapNat]
  show _ = AssociatedGraded.homogeneousSMul (I.ideal U) _ _
  rw [AssociatedGraded.homogeneousSMul_mk]
  exact congrArg (AssociatedGraded.mk (I.ideal U) (k + l))
    (Subtype.ext (reesMultiplication_ambient I (k : ℤ) (l : ℤ) U.1 x y))

/-- The chart maps are multiplicative. -/
theorem reesChartMap_multiplicative :
    Stacks.BasisRestriction.IsMultiplicativeOnBasis (reesGradedAlgebra I) D.algebra
      (fun V : X.affineOpens => V.1) (fun n V => reesChartMap D V n) := by
  intro i j U x y
  dsimp only
  have hzero : ∀ m : ℤ, m < 0 → ∀ z : ((reesGradedAlgebra I).piece m).val.obj (op U.1),
      z = 0 := fun m hm z =>
    sections_eq_zero_of_isZero _ (reesPiece_negative_isZero I m hm) (op U.1) z
  by_cases hi : i < 0
  · rw [hzero i hi x, reesChartMap_of_neg D U hi]
    simp
  by_cases hj : j < 0
  · rw [hzero j hj y, reesChartMap_of_neg D U hj]
    simp
  lift i to ℕ using le_of_not_gt hi
  lift j to ℕ using le_of_not_gt hj
  exact reesChartMapNat_mul D U i j x y


/-! ### The homomorphism of sheaves of graded algebras -/

/-- The affine opens of a scheme, as a basis presented by a family. -/
theorem isBasis_affineOpensVal (X : Scheme.{u}) :
    Opens.IsBasis (Set.range (fun V : X.affineOpens => V.1)) := by
  rw [show (Set.range (fun V : X.affineOpens => V.1)) =
    Set.range (Subtype.val : X.affineOpens → X.Opens) from rfl, Subtype.range_coe]
  exact X.isBasis_affineOpens

/-- The homomorphism of sheaves of graded algebras glued from the chart maps, before unitality
is recorded. -/
def reesToAssociatedGradedHom : reesGradedAlgebra I ⟶ D.algebra :=
  Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis (reesGradedAlgebra I) D.algebra
    (fun V : X.affineOpens => V.1) (fun n V => reesChartMap D V n)
    (isBasis_affineOpensVal X) (reesChartMap_compatible D) (reesChartMap_multiplicative D)

/-- Over an affine open, the glued homomorphism is the chart map. -/
theorem reesToAssociatedGradedHom_app_app (n : ℤ) (V : X.affineOpens) :
    ((reesToAssociatedGradedHom D).app n).val.app (op V.1) = reesChartMap D V n :=
  Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis_app_app _ _ _ _ _ _ _ n V

/-- **The Rees algebra of `ℐ` maps onto its associated graded algebra**, as a unital
homomorphism of sheaves of graded algebras: in degree `n` a section of `ℐⁿ` goes to its class
modulo `ℐⁿ⁺¹`. -/
def reesToAssociatedGraded :
    SheafOfModules.GradedAlgebra.UnitalHom (reesGradedAlgebra I) D.algebra where
  app n := (reesToAssociatedGradedHom D).app n
  map_mul := (reesToAssociatedGradedHom D).map_mul
  map_one U := by
    refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (D.algebra.piece 0)
      (fun V : X.affineOpens => V.1) (isBasis_affineOpensVal X) _ _ (fun V hle => ?_)
    have hnat := PresheafOfModules.naturality_apply
      ((reesToAssociatedGradedHom D).app 0).val (homOfLE hle).op
      ((reesGradedAlgebra I).one.eval U)
    refine hnat.symm.trans ?_
    have hone : ((reesGradedAlgebra I).piece 0).val.map (homOfLE hle).op
        ((reesGradedAlgebra I).one.eval U) = (reesGradedAlgebra I).one.eval (op V.1) :=
      (reesGradedAlgebra I).one.property (homOfLE hle).op
    rw [hone]
    refine Eq.trans ?_ (D.algebra.one.property (homOfLE hle).op).symm
    rw [reesToAssociatedGradedHom_app_app]
    refine (D.algebraPiece 0 V).injective ?_
    refine (algebraPiece_reesChartMap D V 0 _).trans ?_
    refine Eq.trans ?_ (algebraPiece_zero_one D V).symm
    refine congrArg (AssociatedGraded.mk (M := Γ(X, V.1)) (I.ideal V) 0) (Subtype.ext ?_)
    exact reesUnit_ambient I (op V.1)

/-! ### Restriction of scalars for graded modules -/

variable {R B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- The degree-`i` component of a unital homomorphism, read on the sections over an open as an
additive map. -/
def unitalHomSectionHom (q : SheafOfModules.GradedAlgebra.UnitalHom R B) (i : ℤ)
    (U : X.Opensᵒᵖ) : (R.piece i).val.obj U →+ (B.piece i).val.obj U :=
  ((q.app i).val.app U).hom.toAddMonoidHom

/-- `unitalHomSectionHom` applies the degree-`i` component on sections. -/
@[simp]
theorem unitalHomSectionHom_apply (q : SheafOfModules.GradedAlgebra.UnitalHom R B) (i : ℤ)
    (U : X.Opensᵒᵖ) (y : (R.piece i).val.obj U) :
    unitalHomSectionHom q i U y = (q.app i).val.app U y := rfl

/-- **Restriction of scalars for graded modules.** A graded module over the codomain of a unital
homomorphism of sheaves of graded algebras is a graded module over its domain, with the same
homogeneous pieces, acted on through the homomorphism. -/
def restrictGradedModule (q : SheafOfModules.GradedAlgebra.UnitalHom R B)
    (M : SheafOfModules.GradedModule B) : SheafOfModules.GradedModule R where
  piece := M.piece
  smul n i U :=
    { toFun := fun x => (M.smul n i U x).comp (unitalHomSectionHom q i U)
      map_zero' := by ext y; simp
      map_add' := fun x₁ x₂ => by ext y; simp }
  smul_smul_left n i U r x y := by
    simpa using M.smul_smul_left n i U r x ((q.app i).val.app U y)
  smul_smul_right n i U r x y := by
    have h : (q.app i).val.app U (r • y) = r • (q.app i).val.app U y :=
      ((q.app i).val.app U).hom.map_smul r y
    simpa [h] using M.smul_smul_right n i U r x ((q.app i).val.app U y)
  smul_naturality n i U V f x y := by
    have h : (q.app i).val.app V ((R.piece i).val.map f y) =
        (B.piece i).val.map f ((q.app i).val.app U y) :=
      PresheafOfModules.naturality_apply (q.app i).val f y
    change (M.piece (n + i)).val.map f (M.smul n i U x ((q.app i).val.app U y)) =
      M.smul n i V ((M.piece n).val.map f x)
        ((q.app i).val.app V ((R.piece i).val.map f y))
    rw [h]
    exact M.smul_naturality n i f x ((q.app i).val.app U y)
  smul_mul n i j U x y z := by
    have h := q.map_mul i j U y z
    simpa [h] using
      M.smul_mul n i j U x ((q.app i).val.app U y) ((q.app j).val.app U z)
  smul_one n U x := by
    have h := q.map_one U
    simpa [h] using M.smul_one n U x

/-- Restriction of scalars does not change the homogeneous pieces. -/
@[simp]
theorem restrictGradedModule_piece (q : SheafOfModules.GradedAlgebra.UnitalHom R B)
    (M : SheafOfModules.GradedModule B) (n : ℤ) :
    (restrictGradedModule q M).piece n = M.piece n := rfl

/-- After restriction of scalars along `q`, a section acts through its image under `q`. -/
theorem restrictGradedModule_smul (q : SheafOfModules.GradedAlgebra.UnitalHom R B)
    (M : SheafOfModules.GradedModule B) (n i : ℤ) (U : X.Opensᵒᵖ)
    (x : (M.piece n).val.obj U) (y : (R.piece i).val.obj U) :
    (restrictGradedModule q M).smul n i U x y =
      M.smul n i U x ((q.app i).val.app U y) := rfl

/-! ### Surjectivity on affine charts -/

/-- Reading the ambient section is surjective onto the ideal power, over an affine open: the
affine description of the Rees algebra is an equivalence onto `Iᵁⁿ`. -/
theorem surjective_reesAmbientPower (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (reesAmbientPower (I := I) U n) := by
  rintro ⟨cv, hcv⟩
  have hmem : cv ∈ I.ideal U ^ ((n : ℤ)).toNat := by
    rw [AssociatedGraded.ring_power_eq] at hcv
    simpa using hcv
  refine ⟨(reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U).symm ⟨cv, hmem⟩,
    Subtype.ext ?_⟩
  have h := reesPieceAffineEquiv_coe I (n : ℤ) (Int.natCast_nonneg n) U
    ((reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U).symm ⟨cv, hmem⟩)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The chart maps are surjective in nonnegative degrees**: every class modulo `ℐⁿ⁺¹` of a
section over an affine open lifts to a section of `ℐⁿ`. -/
theorem surjective_reesChartMapNat (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (reesChartMapNat D U n) := by
  intro x
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (D.algebraPiece n U x)
  obtain ⟨y, hy⟩ := surjective_reesAmbientPower (I := I) U n c
  refine ⟨y, (D.algebraPiece n U).injective ?_⟩
  rw [algebraPiece_reesChartMapNat, hy]
  exact hc

/-- **The glued homomorphism is surjective on the sections over an affine open**, in every
nonnegative degree: every class modulo `ℐⁿ⁺¹` lifts to a section of `ℐⁿ`. -/
theorem exists_reesToAssociatedGraded_app_eq (U : X.affineOpens) (n : ℕ)
    (a : (D.algebra.piece (n : ℤ)).val.obj (op U.1)) :
    ∃ b : ((reesGradedAlgebra I).piece (n : ℤ)).val.obj (op U.1),
      ((reesToAssociatedGraded D).app (n : ℤ)).val.app (op U.1) b = a := by
  obtain ⟨b, hb⟩ := surjective_reesChartMapNat D U n a
  refine ⟨b, ?_⟩
  have h : ((reesToAssociatedGraded D).app (n : ℤ)).val.app (op U.1) =
      reesChartMap D U (n : ℤ) := reesToAssociatedGradedHom_app_app D (n : ℤ) U
  rw [h]
  exact hb

/-! ### The transition kernels of Tag 087Z over the Rees algebra -/

/-- **`⨁ₙ Ker(F_{n+1} ⟶ F_n)` as a graded module over the Rees algebra `⨁_{n ≥ 0} ℐⁿ`**: the
graded module over the associated graded algebra `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹` of [Stacks, Tag 087Z],
restricted along `Stacks.Coherent.reesToAssociatedGraded`. The homogeneous pieces are
unchanged. -/
def reesTransitionGradedModule {F : CoherentAdicSystems I} (D : AssociatedGradedData I F) :
    SheafOfModules.GradedModule (reesGradedAlgebra I) :=
  restrictGradedModule (reesToAssociatedGraded D.toAssociatedGradedAlgebraData) D.module

/-- The homogeneous pieces of `reesTransitionGradedModule D` are those of `D.module`. -/
@[simp]
theorem reesTransitionGradedModule_piece {F : CoherentAdicSystems I}
    (D : AssociatedGradedData I F) (n : ℤ) :
    (reesTransitionGradedModule D).piece n = D.module.piece n := rfl

/-- A section of the Rees algebra acts on `reesTransitionGradedModule D` through its image in
the associated graded algebra. -/
theorem reesTransitionGradedModule_smul {F : CoherentAdicSystems I}
    (D : AssociatedGradedData I F) (n i : ℤ) (U : X.Opensᵒᵖ)
    (x : (D.module.piece n).val.obj U)
    (y : ((reesGradedAlgebra I).piece i).val.obj U) :
    (reesTransitionGradedModule D).smul n i U x y =
      D.module.smul n i U x
        (((reesToAssociatedGraded D.toAssociatedGradedAlgebraData).app i).val.app U y) := rfl

end Stacks.Coherent

end
