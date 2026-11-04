module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulPowerDefs
import Mathlib
import all Mathlib.CategoryTheory.Limits.HasLimits
public import StacksFrontier.Algebra.NegOnePowSmul

/-!
# Koszul towers with coefficients: the finite exterior-basis formulas

This file gives the explicit finite exterior-basis formulas from which the coefficient Koszul
tower is built, the propositions `KoszulCoefficientTower.FormulaLaws` and
`KoszulCoefficientTower.Verification` recording the laws these formulas satisfy, and the first
identities for the projections, sections, coefficient maps and power transitions.

## Main definitions

* `KoszulCoefficientTower.coefficientKoszulGradedPiece` is the finite product of shifted
  coefficient complexes occurring in a graded piece.

## Implementation notes

The coefficient model is formed from finite products indexed by the exterior basis.  Its total
differential uses the cochain sign on the Koszul summand.  After enlarging the module universe it
is naturally isomorphic to the ordinary tensor product with the cohomologically reindexed Koszul
complex.  The filtration applies `HomologicalComplex.stupidTrunc` to the graded exterior
summands, then restricts the total differential by the termwise inclusions and retractions.
All data are explicit. The verification certificate supplies only proofs of their laws.

## References

* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

/-- The subsets indexing exterior degree `j` in a Koszul complex on `r` elements. -/
public abbrev KoszulBasis (r j : ℕ) := {S : Finset (Fin r) // S.card = j}

/-- The small carrier in total degree `t`: its `S`-component is the coefficient term in
degree `t + |S|`.  Since `Finset (Fin r)` is finite and small, this remains in `Type v`. -/
public abbrev coefficientKoszulTerm {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) : ModuleCat.{v} A :=
  ModuleCat.of A (∀ S : Finset (Fin r), K.X (t + S.card))

/-- The signed total differential on the finite exterior-basis model.  The first summand is
the coefficient differential.  The second is contraction by the sequence, with the sign of
the source coefficient degree `t + |S| + 1`. -/
public noncomputable def coefficientKoszulDifferential {r : ℕ} (f : Fin r → A) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := r) K t ⟶ coefficientKoszulTerm (r := r) K (t + 1) :=
  ModuleCat.ofHom
    { toFun := fun x S ↦
        (K.d (t + S.card) ((t + 1) + S.card)).hom (x S) +
          ∑ i : {i : Fin r // i ∉ S},
            ((-1 : A) ^ (t + S.card + 1).natAbs *
                (-1 : A) ^ (S.filter (· < i.1)).card * f i.1 ^ (n + 1)) •
              ((eqToHom (by
                rw [Finset.card_insert_of_notMem i.2]
                norm_num [Nat.cast_add, Nat.cast_one]
                abel_nf) :
                  K.X (t + (insert i.1 S).card) ⟶ K.X ((t + 1) + S.card))).hom
                    (x (insert i.1 S))
      map_add' := by
        intro x y
        ext S
        simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro a x
        ext S
        simp [smul_add, Finset.smul_sum, smul_smul, mul_comm] }

/-- The component formula for the transition from power `m + 1` to power `n + 1`. -/
public noncomputable def coefficientKoszulTransitionTerm {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := r) K t ⟶ coefficientKoszulTerm (r := r) K t :=
  ModuleCat.ofHom
    { toFun := fun x S ↦ (∏ i ∈ S, f i ^ (m - n)) • x S
      map_add' := by intros; ext; simp
      map_smul' := by
        intro a x
        ext S
        simp only [Pi.smul_apply, smul_smul]
        simp only [RingHom.id_apply]
        rw [mul_comm] }

/-- The component formula for the augmentation: the empty exterior-basis component is the
coefficient term and every nonempty component is zero. -/
public noncomputable def coefficientKoszulUnitTerm {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    K.X t ⟶ coefficientKoszulTerm (r := r) K t :=
  ModuleCat.ofHom (LinearMap.pi fun S ↦ if h : S = ∅ then
    (eqToHom (by subst S; simp) : K.X t ⟶ K.X (t + S.card)).hom else 0)

/-- The termwise inclusion of a stupid truncation. -/
public def stupidTruncProjection (K : CochainComplex (ModuleCat.{v} A) ℤ) (p j : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X j ⟶ K.X j :=
  if h : p ≤ j then
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
      (i := (j - p).toNat) (by
        change p + ((j - p).toNat : ℤ) = j
        rw [Int.toNat_of_nonneg (by omega)]; omega)).hom
  else 0

/-- The termwise retraction onto the surviving terms of a stupid truncation.
This is a map of graded modules, not generally a chain map. -/
public def stupidTruncSection (K : CochainComplex (ModuleCat.{v} A) ℤ) (p j : ℤ) :
    K.X j ⟶ (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X j :=
  if h : p ≤ j then
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
      (i := (j - p).toNat) (by
        change p + ((j - p).toNat : ℤ) = j
        rw [Int.toNat_of_nonneg (by omega)]; omega)).inv
  else 0

/-- A graded summand in Koszul degree `j`, optionally stupid-truncated below `p`.
`none` denotes the untruncated summand. -/
public def truncatedSummand (p : Option ℤ) (j : ℤ) (M : ModuleCat.{v} A) : ModuleCat.{v} A :=
  match p with
  | none => M
  | some p =>
      (((HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) j).obj M).stupidTrunc
        (ComplexShape.embeddingUpIntGE p)).X j

/-- Inclusion of a truncated graded summand. -/
public def truncatedSummandProjection (p : Option ℤ) (j : ℤ) (M : ModuleCat.{v} A) :
    truncatedSummand p j M ⟶ M :=
  match p with
  | none => 𝟙 M
  | some p => stupidTruncProjection _ p j ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j M).hom

/-- Retraction onto a truncated graded summand. -/
public def truncatedSummandSection (p : Option ℤ) (j : ℤ) (M : ModuleCat.{v} A) :
    M ⟶ truncatedSummand p j M :=
  match p with
  | none => 𝟙 M
  | some p => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j M).inv ≫
      stupidTruncSection _ p j

/-- Finite exterior-basis terms of the Koszul-direction stupid filtration.
The truncation is applied to the graded Koszul summands before the total differential is
installed; contraction goes from a summand in degree `j` to one in degree `j + 1`. -/
public abbrev filteredTerm {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) : ModuleCat.{v} A :=
  ModuleCat.of A (∀ S : Finset (Fin r),
    truncatedSummand p (-(S.card : ℤ)) (K.X (t + S.card)))

/-- Inclusion of the surviving exterior-basis terms. -/
public def termProjection {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTerm (r := r) p K t ⟶ coefficientKoszulTerm (r := r) K t :=
  ModuleCat.ofHom (LinearMap.pi fun S ↦
    (truncatedSummandProjection p (-(S.card : ℤ)) (K.X (t + S.card))).hom.comp
      (LinearMap.proj S))

/-- Retraction onto the surviving exterior-basis terms. -/
public def termSection {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := r) K t ⟶ filteredTerm (r := r) p K t :=
  ModuleCat.ofHom (LinearMap.pi fun S ↦
    (truncatedSummandSection p (-(S.card : ℤ)) (K.X (t + S.card))).hom.comp
      (LinearMap.proj S))

/-- Signed total differential, restricted to the stupid filtration and zero off the
cochain shape. -/
public def filteredDifferential {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredTerm (r := r) p K i ⟶ filteredTerm (r := r) p K j :=
  if h : i + 1 = j then
    termProjection p K i ≫ coefficientKoszulDifferential f n K i ≫
      termSection p K (i + 1) ≫ eqToHom (congrArg (filteredTerm (r := r) p K) h)
  else 0

/-- A coefficient chain map acts componentwise on the exterior basis. -/
public def coefficientMapTerm {r : ℕ} {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) (t : ℤ) :
    coefficientKoszulTerm (r := r) K t ⟶ coefficientKoszulTerm (r := r) L t :=
  ModuleCat.ofHom (LinearMap.pi fun S ↦ (g.f (t + S.card)).hom.comp (LinearMap.proj S))

/-- Coefficient maps on the stupid filtration. -/
public def filteredMapTerm {r : ℕ} (p : Option ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    filteredTerm (r := r) p K t ⟶ filteredTerm (r := r) p L t :=
  termProjection p K t ≫ coefficientMapTerm g t ≫ termSection p L t

/-- Arbitrary positive-power transitions on the stupid filtration. -/
public def filteredTransitionTerm {r : ℕ} (f : Fin r → A) (p : Option ℤ) (m n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTerm (r := r) p K t ⟶ filteredTerm (r := r) p K t :=
  termProjection p K t ≫ coefficientKoszulTransitionTerm f m n K t ≫ termSection p K t

/-- The empty-subset augmentation on the stupid filtration. -/
public def filteredUnitTerm {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    K.X t ⟶ filteredTerm (r := r) p K t :=
  coefficientKoszulUnitTerm K t ≫ termSection p K t

/-- The termwise inclusion from cutoff `q` to cutoff `p`. -/
public def filtrationInclusionTerm {r : ℕ} (p q : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTerm (r := r) q K t ⟶ filteredTerm (r := r) p K t :=
  termProjection q K t ≫ termSection p K t

/-- The order of stupid cutoffs, with `none` meaning no lower bound. -/
public def CutoffLE : Option ℤ → Option ℤ → Prop
  | none, _ => True
  | some _, none => False
  | some p, some q => p ≤ q

/-- Universe enlargement on coefficient complexes, using the existing 091Z functor. -/
public abbrev complexUniverseLift :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤
      CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ :=
  (AdicKoszul.moduleUniverseLift A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The usual cohomologically indexed Koszul stage, optionally stupid-truncated. -/
public def standardKoszulStage {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  let E := (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
    (Koszul.seqComplex fun i ↦ f i ^ (n + 1))
  match p with
  | none => E
  | some p => E.stupidTrunc (ComplexShape.embeddingUpIntGE p)

/-- The ordinary tensor comparison model, in the common universe only. -/
public abbrev standardCoefficientKoszulStage {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤
      CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ :=
  complexUniverseLift (A := A) ⋙
    (curriedTensor (CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ)).flip.obj
      (standardKoszulStage (fun i ↦ (ULift.up (f i) : ULift.{v} A)) p n)

/-- The ordered exterior-basis vector in the usual Koszul complex. -/
public def koszulBasisVector {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ)
    (S : Finset (Fin r)) : (standardKoszulStage f p n).X (-(S.card : ℤ)) :=
  let e := ((Pi.basisFun A (Fin r)).exteriorPower S.card) ⟨S, rfl⟩
  let x := (HomologicalComplex.extendXIso
    (Koszul.seqComplex fun i ↦ f i ^ (n + 1)) ComplexShape.embeddingDownNat
      (i := S.card) rfl).inv e
  match p with
  | none => x
  | some p => stupidTruncSection _ p (-(S.card : ℤ)) x

/-- The explicit comparison map on terms: send a coefficient in the `S` component to its
tensor with the ordered wedge `e_S`, then include that bidegree in the tensor total complex. -/
public def comparisonTerm {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    (AdicKoszul.moduleUniverseLift A).obj (filteredTerm (r := r) p K t) ⟶
      ((standardCoefficientKoszulStage f p n).obj K).X t :=
  ∑ S : Finset (Fin r),
    (AdicKoszul.moduleUniverseLift A).map
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) ≫
    ModuleCat.ofHom
      ((TensorProduct.mk (ULift.{v} A) _ _).flip
        (koszulBasisVector (fun i ↦ (ULift.up (f i) : ULift.{v} A)) p n S)) ≫
    HomologicalComplex.ιTensorObj ((complexUniverseLift (A := A)).obj K)
      (standardKoszulStage (fun i ↦ (ULift.up (f i) : ULift.{v} A)) p n)
      (t + S.card) (-(S.card : ℤ)) t (by omega)

/-- The graded term in Koszul degree `p ≤ 0`, as a finite product of coefficient shifts. -/
public def coefficientKoszulGradedPiece (r : ℕ) (p : ℤ) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤ CochainComplex (ModuleCat.{v} A) ℤ :=
  shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p) ⋙
    piFunctor.{0} ⋙
      (evaluation (Type 0)ᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj
        (Opposite.op (KoszulBasis r p.natAbs))

/-- The diagonal scalar transition on a graded piece. -/
public def coefficientKoszulGradedTransition {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (coefficientKoszulGradedPiece (A := A) r p).obj K ⟶
      (coefficientKoszulGradedPiece (A := A) r p).obj K :=
  Limits.Pi.map (fun S : KoszulBasis r p.natAbs ↦
    (shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)).map
      ((∏ i ∈ S.1, f i) • 𝟙 K))

/-- Projection onto an associated-graded subset, with the sign identifying its coefficient
complex with the standard signed shift. -/
public def gradedComponentTerm {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) (t : ℤ) :
    filteredTerm (r := r) (some p) K t ⟶ (K⟦-p⟧).X t :=
  ((-1 : A) ^ (t * (-p)).natAbs) •
    (termProjection (some p) K t ≫ ModuleCat.ofHom (LinearMap.proj S.1) ≫
      (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.1.card)
        (by simp [S.2, abs_of_nonpos hp])).inv)

/-- Canonical 0BKC transition on the optionally truncated Koszul complex. -/
public def standardKoszulTransition {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (m n : ℕ) (h : n ≤ m) : standardKoszulStage f p m ⟶ standardKoszulStage f p n :=
  let g := (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).map
    (AdicKoszul.koszulPowerTransition f m n h)
  match p with
  | none => g
  | some p => HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE p)

/-- Inclusion of the optional stupid truncation, on Koszul terms. -/
public def standardKoszulProjectionTerm {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) (j : ℤ) : (standardKoszulStage f p n).X j ⟶
      (standardKoszulStage f none n).X j :=
  match p with
  | none => 𝟙 _
  | some p => stupidTruncProjection _ p j

/-- Retraction onto the optional stupid truncation, on Koszul terms. -/
public def standardKoszulSectionTerm {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) (j : ℤ) : (standardKoszulStage f none n).X j ⟶
      (standardKoszulStage f p n).X j :=
  match p with
  | none => 𝟙 _
  | some p => stupidTruncSection _ p j

/-- The prescribed term map between two stupid truncations of the usual Koszul complex. -/
public def standardKoszulInclusionTerm {r : ℕ} (f : Fin r → A) (p q : Option ℤ)
    (n : ℕ) (j : ℤ) : (standardKoszulStage f q n).X j ⟶
      (standardKoszulStage f p n).X j :=
  standardKoszulProjectionTerm f q n j ≫ standardKoszulSectionTerm f p n j

/-- Algebraic identities for the fixed finite-basis formulas.  This is proof data only:
objects, differentials, maps, and comparison maps have already been specified above. -/
public structure FormulaLaws {r : ℕ} (f : Fin r → A) : Prop where
  square (p n) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j k : ℤ) :
    filteredDifferential f p n K i j ≫ filteredDifferential f p n K j k = 0
  map_comm (p n) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (i j : ℤ) :
    filteredMapTerm (r := r) p g i ≫ filteredDifferential f p n L i j =
      filteredDifferential f p n K i j ≫ filteredMapTerm p g j
  map_id (p) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredMapTerm (r := r) p (𝟙 K) t = 𝟙 _
  map_comp (p) {K L M : CochainComplex (ModuleCat.{v} A) ℤ}
      (g : K ⟶ L) (h : L ⟶ M) (t : ℤ) :
    filteredMapTerm (r := r) p (g ≫ h) t =
      filteredMapTerm p g t ≫ filteredMapTerm p h t
  transition_comm (p m n) (h : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredTransitionTerm f p m n K i ≫ filteredDifferential f p n K i j =
      filteredDifferential f p m K i j ≫ filteredTransitionTerm f p m n K j
  transition_id (p n) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f p n n K t = 𝟙 _
  transition_comp (p k m n) (hkm : m ≤ k) (hmn : n ≤ m)
      (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f p k n K t =
      filteredTransitionTerm f p k m K t ≫ filteredTransitionTerm f p m n K t
  transition_naturality (p m n) (h : n ≤ m)
      {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    filteredTransitionTerm f p m n K t ≫ filteredMapTerm p g t =
      filteredMapTerm p g t ≫ filteredTransitionTerm f p m n L t
  unit_comm (p n) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredUnitTerm (r := r) p K i ≫ filteredDifferential f p n K i j =
      K.d i j ≫ filteredUnitTerm p K j
  unit_naturality (p) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    g.f t ≫ filteredUnitTerm (r := r) p L t =
      filteredUnitTerm p K t ≫ filteredMapTerm p g t
  unit_transition (p m n) (h : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredUnitTerm (r := r) p K t ≫ filteredTransitionTerm f p m n K t =
      filteredUnitTerm p K t
  inclusion_comm (p q) (hpq : CutoffLE p q) (n)
      (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filtrationInclusionTerm (r := r) p q K i ≫ filteredDifferential f p n K i j =
      filteredDifferential f q n K i j ≫ filtrationInclusionTerm p q K j
  inclusion_naturality (p q) (hpq : CutoffLE p q)
      {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    filteredMapTerm (r := r) q g t ≫ filtrationInclusionTerm p q L t =
      filtrationInclusionTerm p q K t ≫ filteredMapTerm p g t
  inclusion_transition (p q) (hpq : CutoffLE p q) (m n) (h : n ≤ m)
      (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f q m n K t ≫ filtrationInclusionTerm p q K t =
      filtrationInclusionTerm p q K t ≫ filteredTransitionTerm f p m n K t
  comparison_comm (p n) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    comparisonTerm f p n K i ≫ ((standardCoefficientKoszulStage f p n).obj K).d i j =
      (AdicKoszul.moduleUniverseLift A).map (filteredDifferential f p n K i j) ≫
        comparisonTerm f p n K j
  standard_inclusion_comm (p q) (hpq : CutoffLE p q) (n) (i j : ℤ) :
    standardKoszulInclusionTerm (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p q n i ≫
        (standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p n).d i j =
      (standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) q n).d i j ≫
        standardKoszulInclusionTerm (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p q n j
  graded_comm (p) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ)
      (S : KoszulBasis r p.natAbs) (n) (i j : ℤ) :
    gradedComponentTerm p hp K S i ≫ (K⟦-p⟧).d i j =
      filteredDifferential f (some p) n K i j ≫ gradedComponentTerm p hp K S j
  graded_vanish (p) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ)
      (S : KoszulBasis r p.natAbs) (t : ℤ) :
    filtrationInclusionTerm (r := r) (some p) (some (p + 1)) K t ≫
      gradedComponentTerm p hp K S t = 0

namespace FormulaLaws

variable {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)

/-- The complex with the prescribed signed finite-basis differential. -/
public def stage (p : Option ℤ) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    CochainComplex (ModuleCat.{v} A) ℤ where
  X := filteredTerm (r := r) p K
  d := filteredDifferential f p n K
  shape i j hij := by
    apply dite_eq_right
    exact hij
  d_comp_d' i j k _ _ := h.square p n K i j k

/-- The chain map acting componentwise on coefficients. -/
public def stageMap (p : Option ℤ) (n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    h.stage p n K ⟶ h.stage p n L where
  f := filteredMapTerm p g
  comm' i j _ := h.map_comm p n g i j

/-- The diagonal chain map from power `m + 1` to power `n + 1`. -/
public def transition (p : Option ℤ) (m n : ℕ) (hmn : n ≤ m)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) : h.stage p m K ⟶ h.stage p n K where
  f := filteredTransitionTerm f p m n K
  comm' i j _ := h.transition_comm p m n hmn K i j

/-- The strictly functorial tower formed from the prescribed maps. -/
public def tower (p : Option ℤ) : CochainComplex (ModuleCat.{v} A) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) where
  obj K :=
    { obj n := h.stage p n.unop K
      map g := h.transition p _ _ (leOfHom g.unop) K
      map_id n := HomologicalComplex.hom_ext _ _ (h.transition_id p n.unop K)
      map_comp g g' := HomologicalComplex.hom_ext _ _
        (h.transition_comp p _ _ _ (leOfHom g.unop) (leOfHom g'.unop) K) }
  map g :=
    { app n := h.stageMap p n.unop g
      naturality _ _ a := HomologicalComplex.hom_ext _ _
        (h.transition_naturality p _ _ (leOfHom a.unop) g) }
  map_id K := NatTrans.ext <| funext fun _ ↦ HomologicalComplex.hom_ext _ _ (h.map_id p K)
  map_comp g g' := NatTrans.ext <| funext fun _ ↦ HomologicalComplex.hom_ext _ _ (h.map_comp p g g')

/-- The compatible natural empty-subset augmentation. -/
public def augmentation (p : Option ℤ) :
    (Functor.const ℕᵒᵖ).obj (𝟭 (CochainComplex (ModuleCat.{v} A) ℤ)) ⟶
      (h.tower p).flip :=
  { app n :=
      { app K :=
          { f := filteredUnitTerm p K
            comm' i j _ := h.unit_comm p n.unop K i j }
        naturality _ _ g := HomologicalComplex.hom_ext _ _ (h.unit_naturality p g) }
    naturality _ _ a := NatTrans.ext <| funext fun K ↦ HomologicalComplex.hom_ext _ _ fun t ↦
      (h.unit_transition p _ _ (leOfHom a.unop) K t).symm }

/-- Inclusion between two stupid cutoffs, natural in coefficients and in the power. -/
public def inclusion (p q : Option ℤ) (hpq : CutoffLE p q) : h.tower q ⟶ h.tower p where
  app K :=
    { app n :=
        { f := filtrationInclusionTerm p q K
          comm' i j _ := h.inclusion_comm p q hpq n.unop K i j }
      naturality _ _ a := HomologicalComplex.hom_ext _ _
        (h.inclusion_transition p q hpq _ _ (leOfHom a.unop) K) }
  naturality _ _ g := NatTrans.ext <| funext fun _ ↦
    HomologicalComplex.hom_ext _ _ (h.inclusion_naturality p q hpq g)

/-- The specified wedge comparison, as a chain map. -/
public def comparisonMap (p : Option ℤ) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).obj (h.stage p n K) ⟶
      (standardCoefficientKoszulStage f p n).obj K where
  f := comparisonTerm f p n K
  comm' i j _ := h.comparison_comm p n K i j

/-- Inclusion between the usual stupid-truncated Koszul complexes. -/
public def standardInclusion (p q : Option ℤ) (hpq : CutoffLE p q) (n : ℕ) :
    standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) q n ⟶
      standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p n where
  f := standardKoszulInclusionTerm (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p q n
  comm' i j _ := h.standard_inclusion_comm p q hpq n i j

/-- Projection onto the graded coefficient shifts. -/
public def gradedProjection (p : ℤ) (hp : p ≤ 0) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    h.stage (some p) n K ⟶ (coefficientKoszulGradedPiece (A := A) r p).obj K :=
  Limits.Pi.lift fun S ↦
    { f := gradedComponentTerm p hp K S
      comm' i j _ := h.graded_comm p hp K S n i j }

set_option backward.isDefEq.respectTransparency false in
/-- The induced canonical map from the graded quotient to the coefficient shifts. -/
public def gradedMap (p : ℤ) (hp : p ≤ 0) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    cokernel (((h.inclusion (some p) (some (p + 1)) (by dsimp [CutoffLE]; omega)).app K).app ⟨n⟩) ⟶
      (coefficientKoszulGradedPiece (A := A) r p).obj K :=
  cokernel.desc _ (h.gradedProjection p hp n K) (by
    dsimp only [inclusion, tower]
    apply Limits.Pi.hom_ext
    intro S
    rw [Category.assoc, gradedProjection, Limits.Pi.lift_π, Limits.zero_comp]
    exact HomologicalComplex.hom_ext _ _ (h.graded_vanish p hp K S))

end FormulaLaws

/-- Verification of the explicit comparison and graded quotient maps.  Every map in this
proposition is fixed by its component formula; no object or morphism is selected by it. -/
public structure Verification {r : ℕ} (f : Fin r → A) (h : FormulaLaws.{u, v} f) : Prop where
  comparison_isIso (p n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (h.comparisonMap p n K)
  comparison_naturality (p n) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    (complexUniverseLift (A := A)).map (h.stageMap p n g) ≫ h.comparisonMap p n L =
      h.comparisonMap p n K ≫ (standardCoefficientKoszulStage f p n).map g
  comparison_transition (p m n) (hmn : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (h.transition p m n hmn K) ≫ h.comparisonMap p n K =
      h.comparisonMap p m K ≫
        (𝟙 ((complexUniverseLift (A := A)).obj K) ⊗ₘ
          standardKoszulTransition (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p m n hmn)
  comparison_augmentation (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (((h.augmentation none).app ⟨n⟩).app K) ≫
        h.comparisonMap none n K =
      (MonoidalCategory.rightUnitor ((complexUniverseLift (A := A)).obj K)).inv ≫
        (((complexUniverseLift (A := A)).obj K) ◁
          AdicKoszul.koszulPowerUnit (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n)
  comparison_inclusion (p q) (hpq : CutoffLE p q) (n)
      (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (((h.inclusion p q hpq).app K).app ⟨n⟩) ≫
        h.comparisonMap p n K =
      h.comparisonMap q n K ≫
        (𝟙 ((complexUniverseLift (A := A)).obj K) ⊗ₘ h.standardInclusion p q hpq n)
  inclusion_comp (p q s) (hpq : CutoffLE p q) (hqs : CutoffLE q s) (hps : CutoffLE p s) :
    h.inclusion q s hqs ≫ h.inclusion p q hpq = h.inclusion p s hps
  augmentation_factor (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (((h.augmentation (some 0)).app ⟨n⟩).app K) ≫
        (((h.inclusion none (some 0) trivial).app K).app ⟨n⟩) =
      (((h.augmentation none).app ⟨n⟩).app K)
  augmentation_zero_isIso (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (((h.augmentation (some 0)).app ⟨n⟩).app K)
  filtration_exhaustive (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (((h.inclusion none (some (-(r : ℤ))) trivial).app K).app ⟨n⟩)
  filtration_bounded (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsZero (h.stage (some 1) n K)
  inclusion_mono (p : ℤ) (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    Mono (((h.inclusion (some p) (some (p + 1)) (by dsimp [CutoffLE]; omega)).app K).app ⟨n⟩)
  graded_isIso (p) (hp : p ≤ 0) (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (h.gradedMap p hp n K)
  graded_naturality (p) (hp : p ≤ 0) (n)
      {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    h.stageMap (some p) n g ≫ h.gradedProjection p hp n L =
      h.gradedProjection p hp n K ≫ (coefficientKoszulGradedPiece (A := A) r p).map g
  graded_transition (p) (hp : p ≤ 0) (n) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    h.transition (some p) (n + 1) n (Nat.le_succ n) K ≫ h.gradedProjection p hp n K =
      h.gradedProjection p hp (n + 1) K ≫ coefficientKoszulGradedTransition f p K
  map_quasiIso (p n) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (h.stageMap p n g)

end KoszulCoefficientTower
end

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

private theorem truncatedSummand_isZero (p j : ℤ) (M : ModuleCat.{v} A) (h : j < p) :
    IsZero (truncatedSummand (some p) j M) := by
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro i
  show p + (i : ℤ) ≠ j
  omega

private theorem truncatedSummand_projection_section (p : Option ℤ) (j : ℤ)
    (M : ModuleCat.{v} A) :
    truncatedSummandProjection p j M ≫ truncatedSummandSection p j M = 𝟙 _ := by
  cases p with
  | none => simp [truncatedSummandProjection, truncatedSummandSection, truncatedSummand]
  | some p =>
    by_cases h : p ≤ j
    · simp [truncatedSummandProjection, truncatedSummandSection,
        stupidTruncProjection, stupidTruncSection, h, truncatedSummand,
        Category.assoc, Iso.hom_inv_id]
    · exact (truncatedSummand_isZero p j M (by omega)).eq_of_src _ _

private theorem truncatedSummand_section_projection (p : Option ℤ) (j : ℤ)
    (M : ModuleCat.{v} A) :
    truncatedSummandSection p j M ≫ truncatedSummandProjection p j M =
      (by classical exact if CutoffLE p (some j) then 𝟙 M else 0) := by
  classical
  cases p with
  | none => simp [truncatedSummandProjection, truncatedSummandSection, truncatedSummand, CutoffLE]
  | some p =>
    by_cases h : p ≤ j <;>
      simp [truncatedSummandProjection, truncatedSummandSection,
        stupidTruncProjection, stupidTruncSection, truncatedSummand, CutoffLE, h,
        Category.assoc, Iso.inv_hom_id_assoc, zero_comp, comp_zero]

private theorem truncatedSummandProjection_eq_zero (p : Option ℤ) (j : ℤ)
    (M : ModuleCat.{v} A) (h : ¬ CutoffLE p (some j)) :
    truncatedSummandProjection p j M = 0 := by
  cases p with
  | none => exact (h trivial).elim
  | some p => exact (truncatedSummand_isZero p j M (lt_of_not_ge h)).eq_of_src _ _

private theorem truncatedSummand_map_projection (p : Option ℤ) (j : ℤ)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    truncatedSummandProjection p j M ≫ g ≫ truncatedSummandSection p j N ≫
        truncatedSummandProjection p j N = truncatedSummandProjection p j M ≫ g := by
  rw [truncatedSummand_section_projection]
  by_cases h : CutoffLE p (some j)
  · simp [h, Category.comp_id]
  · simp [h, truncatedSummandProjection_eq_zero p j M h, zero_comp, comp_zero]

/-- Two maps between finite exterior-basis products are equal if they agree on each component. -/
private theorem pi_hom_ext {ι : Type} {F G : ι → ModuleCat.{v} A}
    {f g : ModuleCat.of A (∀ i, F i) ⟶ ModuleCat.of A (∀ i, G i)}
    (h : ∀ x i, f x i = g x i) : f = g :=
  ConcreteCategory.hom_ext _ _ fun x ↦ funext (h x)

private theorem term_projection_section {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    termProjection (r := r) p K t ≫ termSection p K t = 𝟙 _ :=
  pi_hom_ext fun x S ↦ ConcreteCategory.congr_hom
    (truncatedSummand_projection_section p (-(S.card : ℤ)) (K.X (t + S.card))) (x S)

private theorem termProjection_none {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    termProjection (r := r) none K t = 𝟙 _ := rfl

private theorem termSection_none {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    termSection (r := r) none K t = 𝟙 _ := rfl

private theorem coefficientMapTerm_id {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientMapTerm (r := r) (𝟙 K) t = 𝟙 _ := rfl

private theorem coefficientMapTerm_comp {r : ℕ}
    {K L M : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (h : L ⟶ M) (t : ℤ) :
    coefficientMapTerm (r := r) (g ≫ h) t =
      coefficientMapTerm g t ≫ coefficientMapTerm h t := rfl

private theorem filteredMapTerm_id {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredMapTerm (r := r) p (𝟙 K) t = 𝟙 _ := by
  simp only [filteredMapTerm, coefficientMapTerm_id, Category.id_comp, term_projection_section]

private theorem coefficientKoszulTransitionTerm_id {r : ℕ} (f : Fin r → A) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTransitionTerm f n n K t = 𝟙 _ := by
  refine pi_hom_ext fun x S ↦ ?_
  simp [coefficientKoszulTransitionTerm]

private theorem filteredTransitionTerm_id {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f p n n K t = 𝟙 _ := by
  simp only [filteredTransitionTerm, coefficientKoszulTransitionTerm_id,
    Category.id_comp, term_projection_section]

private theorem coefficientKoszulTransitionTerm_comp {r : ℕ} (f : Fin r → A)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTransitionTerm f k n K t =
      coefficientKoszulTransitionTerm f k m K t ≫ coefficientKoszulTransitionTerm f m n K t := by
  refine pi_hom_ext fun x S ↦ ?_
  show (∏ i ∈ S, f i ^ (k - n)) • x S =
    (∏ i ∈ S, f i ^ (m - n)) • ((∏ i ∈ S, f i ^ (k - m)) • x S)
  rw [smul_smul, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  omega

private theorem coefficientKoszulTransitionTerm_naturality {r : ℕ} (f : Fin r → A)
    (m n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    coefficientKoszulTransitionTerm f m n K t ≫ coefficientMapTerm g t =
      coefficientMapTerm g t ≫ coefficientKoszulTransitionTerm f m n L t := by
  refine pi_hom_ext fun x S ↦ ?_
  exact (g.f (t + S.card)).hom.map_smul _ _

private theorem filteredTerm_hom_ext {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) {M : ModuleCat.{v} A}
    {g h : M ⟶ filteredTerm (r := r) p K t}
    (heq : g ≫ termProjection p K t = h ≫ termProjection p K t) : g = h := by
  have := congrArg (fun a ↦ a ≫ termSection (r := r) p K t) heq
  simpa only [Category.assoc, term_projection_section, Category.comp_id] using this

private theorem filteredMapTerm_projection {r : ℕ} (p : Option ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    filteredMapTerm (r := r) p g t ≫ termProjection p L t =
      termProjection p K t ≫ coefficientMapTerm g t :=
  pi_hom_ext fun x S ↦ ConcreteCategory.congr_hom
    (truncatedSummand_map_projection p (-(S.card : ℤ)) (g.f (t + S.card))) (x S)

private theorem filteredMapTerm_comp {r : ℕ} (p : Option ℤ)
    {K L M : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (h : L ⟶ M) (t : ℤ) :
    filteredMapTerm (r := r) p (g ≫ h) t =
      filteredMapTerm p g t ≫ filteredMapTerm p h t := by
  apply filteredTerm_hom_ext p M t
  simp only [Category.assoc, filteredMapTerm_projection, coefficientMapTerm_comp]
  simp only [← Category.assoc, filteredMapTerm_projection]

private theorem filteredTransitionTerm_projection {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f p m n K t ≫ termProjection p K t =
      termProjection p K t ≫ coefficientKoszulTransitionTerm f m n K t :=
  pi_hom_ext fun x S ↦ ConcreteCategory.congr_hom
    (truncatedSummand_map_projection p (-(S.card : ℤ))
      ((∏ i ∈ S, f i ^ (m - n)) • 𝟙 (K.X (t + S.card)))) (x S)

private theorem filteredTransitionTerm_comp {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f p k n K t =
      filteredTransitionTerm f p k m K t ≫ filteredTransitionTerm f p m n K t := by
  apply filteredTerm_hom_ext p K t
  simp only [Category.assoc, filteredTransitionTerm_projection,
    coefficientKoszulTransitionTerm_comp f k m n hkm hmn]
  simp only [← Category.assoc, filteredTransitionTerm_projection]

private theorem filteredTransitionTerm_naturality {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (m n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    filteredTransitionTerm f p m n K t ≫ filteredMapTerm p g t =
      filteredMapTerm p g t ≫ filteredTransitionTerm f p m n L t := by
  apply filteredTerm_hom_ext p L t
  simp only [Category.assoc, filteredMapTerm_projection, filteredTransitionTerm_projection]
  simp only [← Category.assoc, filteredMapTerm_projection, filteredTransitionTerm_projection]
  simp only [Category.assoc, coefficientKoszulTransitionTerm_naturality]

end KoszulCoefficientTower

end
