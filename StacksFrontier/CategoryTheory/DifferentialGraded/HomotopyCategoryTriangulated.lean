module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeTriangleComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.Octahedron
public import StacksFrontier.CategoryTheory.DifferentialGraded.RotatedConeTriangle

/-!
# The homotopy category of a differential graded category with cones is triangulated

Let `A` be a differential graded category satisfying the direct-sum axiom (A), the shift axiom
(B) and the cone axiom (C). Its homotopy category `K(A)` is preadditive, has the zero
object of axiom (A), carries the translation functors of axiom (B), and becomes a triangulated
category when its distinguished triangles are declared to be exactly those isomorphic to the
triangle `x → y → z → x[1]` of an admissible short exact sequence, the last arrow being the
connecting morphism `π d(s)`.

Axiom (B) is taken in its isomorphism-valued form `DGCategory.ConeSituationIso`, in which the
shift is additive on objects only up to isomorphism, together with the round-trip coherence
`DGCategory.ShiftAxiomBIso.RoundTripCoherent`. That is what the differential graded category of
complexes satisfies, and the strict `DGCategory.ConeSituation` is a special case whose coherence
is automatic, so each declaration has a strict form at the end of the file.

## Main definitions

* `DGCategory.homotopyPreadditive`: the preadditive structure on `K(A)`.
* `DGCategory.IsDistinguishedTriangleIso`: the triangles isomorphic to the triangle of an
  admissible short exact sequence.
* `DGCategory.homotopyPretriangulatedIso`: the pretriangulated structure on `K(A)` whose
  distinguished triangles are exactly those.

## Main results

* `DGCategory.homotopyPreadditive_mk_add` and `DGCategory.homotopyPreadditive_zero`: the sum
  and the zero of that preadditive structure, read on representing cocycles.
* `DGCategory.homotopyHasZeroObjectIso` and `DGCategory.homotopyShiftAdditiveIso`: the remaining
  structures that the pretriangulated axioms require.
* `DGCategory.distinguishedTriangles_homotopyPretriangulatedIso`: the distinguished triangles of
  that structure are the triangles of admissible short exact sequences.
* `DGCategory.homotopyCategory_isTriangulatedIso`: the octahedron axiom, so `K(A)` is a
  triangulated category.
* `DGCategory.homotopyHasZeroObject`, `DGCategory.homotopyShiftAdditive`,
  `DGCategory.IsDistinguishedTriangle`, `DGCategory.homotopyPretriangulated`,
  `DGCategory.distinguishedTriangles_homotopyPretriangulated` and
  `DGCategory.homotopyCategory_isTriangulated`: the same over the strict
  `DGCategory.ConeSituation`.

## References

* [Stacks Project, Tag 09QW](https://stacks.math.columbia.edu/tag/09QW)
* [Stacks Project, Tag 09QY](https://stacks.math.columbia.edu/tag/09QY)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open GradedSplitShortExact (comp_connectingHom comp_zero connectingHom connectingHom_comp)

universe u v w

variable {R : Type w} [CommRing R] (A : DGCategory.{v, u} R)
  (S : ConeSituationIso A)

/-- The differential commutes with negation. -/
private theorem d_neg_eq {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : A.d (-f) = -A.d f := by
  rw [← neg_one_smul R f, A.d_smul, neg_one_smul]

@[instance_reducible]
private def cocycleZero (x y : A.Obj) : Zero (A.Cocycle x y) := ⟨⟨0, A.d_zero⟩⟩

@[instance_reducible]
private def cocycleAdd (x y : A.Obj) : Add (A.Cocycle x y) :=
  ⟨fun f g => ⟨f.1 + g.1, by rw [A.d_add, f.2, g.2, add_zero]⟩⟩

@[instance_reducible]
private def cocycleNeg (x y : A.Obj) : Neg (A.Cocycle x y) :=
  ⟨fun f => ⟨-f.1, by rw [d_neg_eq, f.2, neg_zero]⟩⟩

@[instance_reducible]
private def cocycleSub (x y : A.Obj) : Sub (A.Cocycle x y) :=
  ⟨fun f g => ⟨f.1 - g.1, by
    rw [sub_eq_add_neg, A.d_add, d_neg_eq, f.2, g.2, neg_zero, add_zero]⟩⟩

@[instance_reducible]
private def cocycleNatSMul (x y : A.Obj) : SMul ℕ (A.Cocycle x y) where
  smul n f := ⟨n • f.1, by
    induction n with
    | zero => simp [A.d_zero]
    | succ n hn => rw [succ_nsmul, A.d_add, hn, f.2, add_zero]⟩

@[instance_reducible]
private def cocycleIntSMul (x y : A.Obj) : SMul ℤ (A.Cocycle x y) where
  smul n f := ⟨n • f.1, by
    rw [← Int.cast_smul_eq_zsmul R n f.1, A.d_smul, f.2, smul_zero]⟩

attribute [local instance] cocycleZero cocycleAdd cocycleNeg cocycleSub cocycleNatSMul
  cocycleIntSMul

@[instance_reducible]
private def cocycleAddK (x y : A.K) : Add (A.Cocycle (x : A.Obj) (y : A.Obj)) :=
  cocycleAdd A x y

attribute [local instance] cocycleAddK

@[instance_reducible]
private noncomputable def cocycleAddCommGroup (x y : A.Obj) : AddCommGroup (A.Cocycle x y) :=
  Function.Injective.addCommGroup (fun f : A.Cocycle x y => f.1) Subtype.val_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

attribute [local instance] cocycleAddCommGroup

private def homotopyBoundaries (x y : A.Obj) : AddSubgroup (A.Cocycle x y) where
  carrier := {f | ∃ h : A.Hom x y (-1),
    f.1 = A.d' (show (-1 : ℤ) + 1 = 0 by omega) h}
  zero_mem' := ⟨0, by
    change (0 : A.Hom x y 0) = A.d' (show (-1 : ℤ) + 1 = 0 by omega) (0 : A.Hom x y (-1))
    simpa [d'] using
      (d_zero (A := A) (x := x) (y := y) (n := -1)).symm⟩
  add_mem' := by
    rintro f g ⟨f', hf⟩ ⟨g', hg⟩
    refine ⟨f' + g', ?_⟩
    change f.1 + g.1 = A.d' (show (-1 : ℤ) + 1 = 0 by omega) (f' + g')
    have hf' : f.1 = A.d f' := by simpa [d'] using hf
    have hg' : g.1 = A.d g' := by simpa [d'] using hg
    simpa only [d'] using (by rw [hf', hg', A.d_add] :
      f.1 + g.1 = A.d (f' + g'))
  neg_mem' := by
    rintro f ⟨h, hh⟩
    refine ⟨-h, ?_⟩
    change -f.1 = A.d' (show (-1 : ℤ) + 1 = 0 by omega) (-h)
    have hh' : f.1 = A.d h := by simpa [d'] using hh
    simp only [d']
    rw [d_neg_eq, ← hh']

private theorem homotopySetoid_eq_boundaries_leftRel (x y : A.Obj) :
    A.homotopySetoid x y = QuotientAddGroup.leftRel (homotopyBoundaries A x y) := by
  apply Setoid.ext
  intro f g
  show A.Homotopic f g ↔ QuotientAddGroup.leftRel (homotopyBoundaries A x y) f g
  rw [QuotientAddGroup.leftRel_apply]
  show (∃ h : A.Hom x y (-1), f.1 - g.1 =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) h) ↔
    -f + g ∈ homotopyBoundaries A x y
  constructor
  · rintro ⟨h, hh⟩
    convert (homotopyBoundaries A x y).neg_mem (show f - g ∈ _ from ⟨h, hh⟩) using 1
    abel
  · intro hmem
    show f - g ∈ homotopyBoundaries A x y
    convert (homotopyBoundaries A x y).neg_mem hmem using 1
    abel

private noncomputable def homotopyClassEquiv (x y : A.Obj) :
    A.HomotopyClass x y ≃ A.Cocycle x y ⧸ homotopyBoundaries A x y :=
  Quotient.congrRight (fun f g => by rw [homotopySetoid_eq_boundaries_leftRel A x y])

@[instance_reducible]
private noncomputable def homotopyClassAddCommGroup (x y : A.Obj) :
    AddCommGroup (A.HomotopyClass x y) := by
  letI : AddCommGroup (A.Cocycle x y ⧸ homotopyBoundaries A x y) := inferInstance
  exact (homotopyClassEquiv A x y).addCommGroup

attribute [local instance] homotopyClassAddCommGroup

@[instance_reducible]
private noncomputable def homotopyClassAddCommGroupK (x y : A.K) :
    AddCommGroup (A.HomotopyClass (x : A.Obj) (y : A.Obj)) :=
  homotopyClassAddCommGroup A x y

attribute [local instance] homotopyClassAddCommGroupK

private theorem homotopyClass_mk_add (x y : A.K)
    (f g : A.Cocycle (x : A.Obj) (y : A.Obj)) :
    Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj)) f +
      Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj)) g =
      Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj)) (f + g) := by
  let e := homotopyClassEquiv A (x : A.Obj) (y : A.Obj)
  let : AddCommGroup (A.Cocycle (x : A.Obj) (y : A.Obj)) :=
    cocycleAddCommGroup A (x : A.Obj) (y : A.Obj)
  let : AddCommGroup (A.Cocycle (x : A.Obj) (y : A.Obj) ⧸
      homotopyBoundaries A (x : A.Obj) (y : A.Obj)) := inferInstance
  let : AddCommGroup (A.HomotopyClass (x : A.Obj) (y : A.Obj)) := e.addCommGroup
  apply e.injective
  show QuotientAddGroup.mk' (homotopyBoundaries A (x : A.Obj) (y : A.Obj)) f +
      QuotientAddGroup.mk' (homotopyBoundaries A (x : A.Obj) (y : A.Obj)) g =
    QuotientAddGroup.mk' (homotopyBoundaries A (x : A.Obj) (y : A.Obj)) (f + g)
  exact ((QuotientAddGroup.mk' _).map_add f g).symm

private theorem homotopyClass_mk_neg (x y : A.K)
    (f : A.Cocycle (x : A.Obj) (y : A.Obj)) :
    Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj))
        ((cocycleNeg A (x : A.Obj) (y : A.Obj)).neg f) =
      -Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj)) f := by
  let e := homotopyClassEquiv A (x : A.Obj) (y : A.Obj)
  let : AddCommGroup (A.Cocycle (x : A.Obj) (y : A.Obj)) :=
    cocycleAddCommGroup A (x : A.Obj) (y : A.Obj)
  let : AddCommGroup (A.Cocycle (x : A.Obj) (y : A.Obj) ⧸
      homotopyBoundaries A (x : A.Obj) (y : A.Obj)) := inferInstance
  let : AddCommGroup (A.HomotopyClass (x : A.Obj) (y : A.Obj)) := e.addCommGroup
  apply e.injective
  show QuotientAddGroup.mk' (homotopyBoundaries A (x : A.Obj) (y : A.Obj))
      ((cocycleNeg A (x : A.Obj) (y : A.Obj)).neg f) =
    -QuotientAddGroup.mk' (homotopyBoundaries A (x : A.Obj) (y : A.Obj)) f
  exact map_neg _ _

private theorem homotopyClass_mk_comp {x y z : A.K}
    (g : A.Cocycle (y : A.Obj) (z : A.Obj))
    (f : A.Cocycle (x : A.Obj) (y : A.Obj)) :
    A.compK (Quotient.mk (A.homotopySetoid (y : A.Obj) (z : A.Obj)) g)
      (Quotient.mk (A.homotopySetoid (x : A.Obj) (y : A.Obj)) f) =
    Quotient.mk (A.homotopySetoid (x : A.Obj) (z : A.Obj))
      (A.compCocycle g f) :=
  rfl

/-- The homotopy category is preadditive: homotopy classes of closed degree-zero morphisms
form an abelian group and composition is bilinear. -/
@[instance_reducible, no_expose]
public noncomputable def homotopyPreadditive : Preadditive A.K := by
  letI (X Y : A.K) : AddCommGroup (A.Cocycle (X : A.Obj) (Y : A.Obj)) :=
    cocycleAddCommGroup A X Y
  letI (X Y : A.K) : AddCommGroup (A.HomotopyClass (X : A.Obj) (Y : A.Obj)) :=
    homotopyClassAddCommGroup A X Y
  refine ⟨fun X Y => homotopyClassAddCommGroup A X Y, ?_, ?_⟩
  · intro X Y Z f f' g
    induction f using Quotient.inductionOn with
    | _ f =>
      induction f' using Quotient.inductionOn with
      | _ f' =>
        induction g using Quotient.inductionOn with
        | _ g =>
          rw [homotopyClass_mk_add (A := A) X Y f f']
          change A.compK
              (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) g)
              (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) (f + f')) =
            A.compK (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) g)
                (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) f) +
              A.compK (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) g)
                (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) f')
          rw [homotopyClass_mk_comp, homotopyClass_mk_comp,
            homotopyClass_mk_comp, homotopyClass_mk_add]
          apply Quotient.sound
          have heq : A.compCocycle g (f + f') =
              A.compCocycle g f + A.compCocycle g f' := by
            apply Subtype.ext
            exact A.comp_add_right (by omega) g.1 f.1 f'.1
          rw [heq]
  · intro X Y Z f g g'
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction g' using Quotient.inductionOn with
        | _ g' =>
          rw [homotopyClass_mk_add (A := A) Y Z g g']
          change A.compK
              (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) (g + g'))
              (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) f) =
            A.compK (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) g)
                (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) f) +
              A.compK (Quotient.mk (A.homotopySetoid (Y : A.Obj) (Z : A.Obj)) g')
                (Quotient.mk (A.homotopySetoid (X : A.Obj) (Y : A.Obj)) f)
          rw [homotopyClass_mk_comp, homotopyClass_mk_comp,
            homotopyClass_mk_comp, homotopyClass_mk_add]
          apply Quotient.sound
          have heq : A.compCocycle (g + g') f =
              A.compCocycle g f + A.compCocycle g' f := by
            apply Subtype.ext
            exact A.comp_add_left (by omega) g.1 g'.1 f.1
          rw [heq]

/-- The sum of two morphisms of the preadditive structure on `K(A)` is the class of the sum of
any two representing cocycles. -/
public theorem homotopyPreadditive_mk_add (x y : A.Obj) (f g : A.Cocycle x y) :
    letI : AddCommGroup (A.HomotopyClass x y) := (homotopyPreadditive A).homGroup x y
    Quotient.mk (A.homotopySetoid x y) f + Quotient.mk (A.homotopySetoid x y) g =
      Quotient.mk (A.homotopySetoid x y) ⟨f.1 + g.1, by rw [A.d_add, f.2, g.2, add_zero]⟩ :=
  homotopyClass_mk_add A x y f g

/-- The zero morphism of the preadditive structure on `K(A)` is the class of the zero
cocycle. -/
public theorem homotopyPreadditive_zero (x y : A.Obj) :
    letI : AddCommGroup (A.HomotopyClass x y) := (homotopyPreadditive A).homGroup x y
    (0 : A.HomotopyClass x y) = Quotient.mk (A.homotopySetoid x y) ⟨0, A.d_zero⟩ := by
  let : AddCommGroup (A.HomotopyClass x y) := (homotopyPreadditive A).homGroup x y
  set z : A.HomotopyClass x y :=
    Quotient.mk (A.homotopySetoid x y) ⟨0, A.d_zero⟩ with hz
  have h : z + z = 0 + z := by
    rw [zero_add, hz, homotopyPreadditive_mk_add]
    exact congrArg (Quotient.mk (A.homotopySetoid x y))
      (Subtype.ext (add_zero (0 : A.Hom x y 0)))
  exact (add_right_cancel h).symm

private theorem homotopyClass_subsingleton (x y : A.Obj)
    (h : Subsingleton (A.Hom x y 0)) : Subsingleton (A.HomotopyClass x y) := by
  let : Subsingleton (A.Cocycle x y) := ⟨fun f g => Subtype.ext (h.elim f.1 g.1)⟩
  infer_instance

private theorem homotopyZeroIsZero (P : Preadditive A.K) :
    letI : Category A.Obj := instCategoryK A
    letI : Preadditive A.K := P
    IsZero (S.directSum.zero : A.K) := by
  let : Preadditive A.K := P
  let z : A.K := S.directSum.zero
  have hz : IsZero z := by
    constructor
    · intro Y
      let : Subsingleton (A.HomotopyClass (z : A.Obj) (Y : A.Obj)) :=
        homotopyClass_subsingleton A z Y (S.directSum.zero_from Y 0)
      exact ⟨{ default := 0, uniq := fun f => Subsingleton.elim _ _ }⟩
    · intro Y
      let : Subsingleton (A.HomotopyClass (Y : A.Obj) (z : A.Obj)) :=
        homotopyClass_subsingleton A Y z (S.directSum.zero_to Y 0)
      exact ⟨{ default := 0, uniq := fun f => Subsingleton.elim _ _ }⟩
  exact hz

include A S in
/-- The zero object of axiom (A) is a zero object of the homotopy category. -/
public theorem homotopyHasZeroObjectIso : HasZeroObject A.K :=
  ⟨⟨S.directSum.zero, homotopyZeroIsZero A S (homotopyPreadditive A)⟩⟩

/-- Each translation functor of the homotopy category is additive. -/
@[sga "4½ Etat_0 1.2.2" "partial"]
public theorem homotopyShiftAdditiveIso (n : ℤ) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasShift A.K ℤ := S.shift.kShift
    (shiftFunctor A.K n).Additive := by
  let : Preadditive A.K := homotopyPreadditive A
  let : HasShift A.K ℤ := S.shift.kShift
  let F := S.shift.shiftFunctor n
  refine ⟨?_⟩
  intro X Y f g
  rw [S.shift.kShift_functor n]
  dsimp only [DGFunctor.onK]
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      rw [homotopyClass_mk_add (A := A) X Y f g]
      dsimp only [DGFunctor.mapHomotopyClass]
      simp only [Quotient.map_mk]
      show Quotient.mk (A.homotopySetoid (F.obj X) (F.obj Y))
          (F.mapCocycle (f + g)) =
        (Quotient.mk (A.homotopySetoid (F.obj X) (F.obj Y)) (F.mapCocycle f) :
          A.HomotopyClass (F.obj X) (F.obj Y)) +
          (Quotient.mk (A.homotopySetoid (F.obj X) (F.obj Y)) (F.mapCocycle g) :
            A.HomotopyClass (F.obj X) (F.obj Y))
      rw [homotopyClass_mk_add (A := A)
        (x := (F.obj X : A.K)) (y := (F.obj Y : A.K))]
      apply Quotient.sound
      have heq : F.mapCocycle (f + g) = F.mapCocycle f + F.mapCocycle g := by
        apply Subtype.ext
        exact F.map_add f.1 g.1
      rw [heq]

private def zeroSplitShortExact (x : A.Obj) :
    GradedSplitShortExact (A := A) x x S.directSum.zero where
  a := ⟨A.id x, A.d_id x⟩
  b := ⟨0, A.d_zero⟩
  π := A.id x
  s := 0
  π_a := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) (A.id x) (A.id x) = A.id x
    exact A.comp_id (A.id x)
  b_s := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) (0 : A.Hom _ _ 0) 0 =
      A.id S.directSum.zero
    rw [A.comp_zero_left]
    exact (S.directSum.zero_to S.directSum.zero 0).elim _ _
  π_s := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) (A.id x) (0 : A.Hom _ _ 0) = 0
    exact A.comp_zero_right _ _
  a_π_add_s_b := by
    change A.comp (by omega : (0 : ℤ) + 0 = 0) (A.id x) (A.id x) +
      A.comp (by omega : (0 : ℤ) + 0 = 0) (0 : A.Hom _ _ 0) 0 = A.id x
    rw [A.comp_id, A.comp_zero_left, add_zero]

/-- A triangle is distinguished if it is isomorphic to one obtained from an
admissible graded-split short exact sequence. -/
public def IsDistinguishedTriangleIso :
    letI : HasShift A.K ℤ := S.shift.kShift
    Pretriangulated.Triangle A.K → Prop := by
  letI : HasShift A.K ℤ := S.shift.kShift
  exact fun T => ∃ (x y z : A.Obj)
    (E : GradedSplitShortExact (A := A) x y z),
      Nonempty (T ≅ S.shift.associatedKTriangle E)

private theorem negativeCone_distinguished {x y : A.Obj} (f : A.Cocycle x y) :
    letI : HasShift A.K ℤ := S.shift.kShift
    IsDistinguishedTriangleIso A S (ConeSituationIso.negativeConeTriangle S f) := by
  let : Preadditive A.K := homotopyPreadditive A
  let : Category A.K := instCategoryK A
  let : Category A.Obj := by
    show Category A.K
    exact instCategoryK A
  let : HasShift A.K ℤ := S.shift.kShift
  obtain ⟨y', z, E, π, s, hπα, hπs, hsπ⟩ :=
    ConeSituationIso.exists_admissibleMono_factorization S f
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
    ConeSituationIso.shortExactTriangleIsoOfFactorization S f E π hπα s hπs hsπ
  let qπ : (y' : A.K) ⟶ (y : A.K) := Quotient.mk (A.homotopySetoid y' y) π
  let qs : (y : A.K) ⟶ (y' : A.K) := Quotient.mk (A.homotopySetoid y y') s
  have hπsK : A.compK qπ qs = Quotient.mk (A.homotopySetoid y y) ⟨A.id y, A.d_id y⟩ := by
    show Quotient.mk (A.homotopySetoid y y) (A.compCocycle π s) = _
    rw [hπs]
  have hsπK : A.compK qs qπ = Quotient.mk (A.homotopySetoid y' y') ⟨A.id y', A.d_id y'⟩ := by
    exact Quotient.sound hsπ
  have hqπ : IsIso qπ := ⟨⟨qs, hsπK, hπsK⟩⟩
  have hφ₁' : IsIso φ.hom₁ := by
    rw [hφ₁]
    show IsIso (𝟙 (x : A.K))
    infer_instance
  have hφ₂' : IsIso φ.hom₂ := by
    rw [hφ₂]
    exact hqπ
  have hφ : IsIso φ :=
    CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos φ hφ₁' hφ₂' hφ₃
  let e : S.shift.associatedKTriangle E ≅
      ConeSituationIso.negativeConeTriangle S f := asIso φ
  exact ⟨x, y', z, E, ⟨e.symm⟩⟩

private theorem negativeCone_rotate_distinguished {x y : A.Obj}
    (f : A.Cocycle x y) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasShift A.K ℤ := S.shift.kShift
    IsDistinguishedTriangleIso A S (ConeSituationIso.negativeConeTriangle S f).rotate := by
  let : Preadditive A.K := homotopyPreadditive A
  let : Category A.K := instCategoryK A
  let : Category A.Obj := instCategoryK A
  let : HasShift A.K ℤ := S.shift.kShift
  let E := S.coneSequence f
  let T := ConeSituationIso.negativeConeTriangle S f
  let U := S.shift.associatedKTriangle E
  have hx : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from x) =
      (show A.K from (S.shift.shiftFunctor 1).obj x) :=
    congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
  let e₃ : T.rotate.obj₃ ≅ U.obj₃ := by
    show (shiftFunctor A.K (1 : ℤ)).obj (show A.K from x) ≅
      (show A.K from (S.shift.shiftFunctor 1).obj x)
    exact {
      hom := -(eqToHom hx)
      inv := -(eqToHom hx.symm)
      hom_inv_id := by
        rw [neg_comp, comp_neg, neg_neg, eqToHom_trans]
        rfl
      inv_hom_id := by
        rw [neg_comp, comp_neg, neg_neg, eqToHom_trans]
        rfl }
  have he : T.rotate ≅ U := by
    refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e₃ ?_ ?_ ?_
    · show A.compK
        (Quotient.mk _ (⟨A.id (S.cone f), A.d_id _⟩ : A.Cocycle _ _))
        (Quotient.mk _ E.a) =
        A.compK (Quotient.mk _ E.a)
          (Quotient.mk _ (⟨A.id y, A.d_id _⟩ : A.Cocycle _ _))
      simp only [compK, Quotient.map₂_mk]
      apply congrArg (Quotient.mk _)
      apply Subtype.ext
      simp [compCocycle, A.id_comp, A.comp_id]
    · let q : (show A.K from S.cone f) ⟶
          (show A.K from (S.shift.shiftFunctor 1).obj x) :=
        Quotient.mk _ E.b
      have hbneg :
          (Quotient.mk (A.homotopySetoid (S.cone f)
            ((S.shift.shiftFunctor 1).obj x))
            (⟨-E.b.1, by
              rw [d_neg_eq, E.b.2, neg_zero]⟩ : A.Cocycle _ _)) = -q :=
        homotopyClass_mk_neg A (show A.K from S.cone f)
          (show A.K from (S.shift.shiftFunctor 1).obj x) E.b
      have ht : T.rotate.mor₂ = (-q) ≫ eqToHom hx.symm := by
        show (Quotient.mk _ (⟨-E.b.1, _⟩ : A.Cocycle _ _)) ≫
          eqToHom hx.symm = _
        rw [hbneg]
      have hu : U.mor₂ = q := rfl
      rw [ht, hu]
      show ((-q) ≫ eqToHom hx.symm) ≫ (-(eqToHom hx)) =
        (𝟙 _) ≫ q
      calc
        ((-q) ≫ eqToHom hx.symm) ≫ (-(eqToHom hx)) =
            -(((-q) ≫ eqToHom hx.symm) ≫ eqToHom hx) := by rw [comp_neg]
        _ = -((-q) ≫ (eqToHom hx.symm ≫ eqToHom hx)) := by
          rw [Category.assoc]
        _ = q := by
          have hcomp : eqToHom hx.symm ≫ eqToHom hx = 𝟙 _ := by
            rw [eqToHom_trans]
            rfl
          rw [hcomp]
          show -(A.compK
            (Quotient.mk _ (⟨A.id _, A.d_id _⟩ : A.Cocycle _ _)) (-q)) = q
          have hid : A.compK
              (Quotient.mk _ (⟨A.id _, A.d_id _⟩ : A.Cocycle _ _)) (-q) = -q := by
            exact (@CategoryTheory.Category.comp_id (A.K) (instCategoryK A)
              _ _ (-q))
          rw [hid, neg_neg]
        _ = (𝟙 _) ≫ q := (Category.id_comp q).symm
    · let qf : (show A.K from x) ⟶ (show A.K from y) :=
        Quotient.mk _ f
      let G := (S.shift.shiftFunctor (1 : ℤ)).onK
      have hy : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from y) =
          (show A.K from (S.shift.shiftFunctor 1).obj y) :=
        congrArg (fun F : A.K ⥤ A.K => F.obj y) (S.shift.kShift_functor 1)
      have hcon : U.mor₃ = G.map qf ≫ eqToHom hy.symm := by
        show (Quotient.mk _ (S.shift.connectingCocycle E)) ≫
          eqToHom hy.symm =
          (Quotient.mk _ ((S.shift.shiftFunctor 1).mapCocycle f)) ≫
            eqToHom hy.symm
        rw [S.cone_connecting f]
      have hmap : eqToHom hx.symm ≫ (shiftFunctor A.K (1 : ℤ)).map qf =
          G.map qf ≫ eqToHom hy.symm := by
        let h₁ : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from x) =
            G.obj (show A.K from x) :=
          congrArg (fun F : A.K ⥤ A.K => F.obj x) (S.shift.kShift_functor 1)
        let h₂ : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from y) =
            G.obj (show A.K from y) :=
          congrArg (fun F : A.K ⥤ A.K => F.obj y) (S.shift.kShift_functor 1)
        show eqToHom h₁.symm ≫ (shiftFunctor A.K (1 : ℤ)).map qf =
          G.map qf ≫ eqToHom h₂.symm
        rw [Functor.congr_hom (S.shift.kShift_functor (1 : ℤ)) qf]
        simp [G]
      have ht : T.rotate.mor₃ = -((shiftFunctor A.K (1 : ℤ)).map qf) := rfl
      rw [ht, hcon, hmap.symm]
      show (-(shiftFunctor A.K (1 : ℤ)).map qf) ≫
          (shiftFunctor A.K (1 : ℤ)).map (𝟙 _) =
        (-(eqToHom hx)) ≫
          (eqToHom hx.symm ≫ (shiftFunctor A.K (1 : ℤ)).map qf)
      have hsid : (shiftFunctor A.K (1 : ℤ)).map (𝟙 (show A.K from y)) =
          𝟙 ((shiftFunctor A.K (1 : ℤ)).obj (show A.K from y)) :=
        (shiftFunctor A.K (1 : ℤ)).map_id _
      rw [hsid]
      calc
        (-(shiftFunctor A.K (1 : ℤ)).map qf) ≫ 𝟙 _ =
            -(shiftFunctor A.K (1 : ℤ)).map qf := by simp
        _ = (-(eqToHom hx ≫ eqToHom hx.symm)) ≫
            (shiftFunctor A.K (1 : ℤ)).map qf := by
          rw [eqToHom_trans]
          simp
        _ = (-(eqToHom hx)) ≫
            (eqToHom hx.symm ≫ (shiftFunctor A.K (1 : ℤ)).map qf) := by
          calc
            (-(eqToHom hx ≫ eqToHom hx.symm)) ≫
                (shiftFunctor A.K (1 : ℤ)).map qf =
                ((-eqToHom hx) ≫ eqToHom hx.symm) ≫
                  (shiftFunctor A.K (1 : ℤ)).map qf := by
                    exact congrArg (fun t => t ≫
                      (shiftFunctor A.K (1 : ℤ)).map qf)
                        (Preadditive.neg_comp _ _).symm
            _ = (-eqToHom hx) ≫
                (eqToHom hx.symm ≫ (shiftFunctor A.K (1 : ℤ)).map qf) :=
                  Category.assoc _ _ _
  exact ⟨y, S.cone f, (S.shift.shiftFunctor 1).obj x, E, ⟨he⟩⟩

/-! ### The inverse rotation of the triangle of an admissible sequence

The middle term of an admissible short exact sequence is homotopy equivalent to the cone of the
desuspended connecting map, by an equivalence that is the identity on the first object. -/

private theorem d_projection {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    A.d E.π = -A.comp (by omega : (1 : ℤ) + 0 = 1)
      (connectingHom E) E.b.1 := by
  have h := connectingHom_comp E
  rw [d_neg_eq] at h
  rw [h]
  simp

private theorem split_map_closed {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} {x y y' z z' : A.Obj}
    (T : GradedSplitShortExact (A := A) x y z)
    (U : GradedSplitShortExact (A := A) x y' z')
    (q : A.Cocycle z z')
    (hδ : A.comp (by omega : (1 : ℤ) + 0 = 1)
      (connectingHom U) q.1 = connectingHom T) :
    A.d (A.comp (by omega : (0 : ℤ) + 0 = 0) U.a.1 T.π +
      A.comp (by omega : (0 : ℤ) + 0 = 0) U.s
        (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 T.b.1)) = 0 := by
  have hδb : A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom U)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 T.b.1) =
      A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom T) T.b.1 := by
    calc
      _ = A.comp (by omega : (1 : ℤ) + 0 = 1)
          (A.comp (by omega : (1 : ℤ) + 0 = 1)
            (connectingHom U) q.1) T.b.1 :=
        A.assoc (l := 1) (m := 0) (n := 0) (p := 0) (q := 1) (r := 1)
          (by omega) (by omega) (by omega) (by omega)
          (connectingHom U) q.1 T.b.1
      _ = _ := by rw [hδ]
  have hterm :
      A.comp (by omega : (1 : ℤ) + 0 = 1)
        (A.comp (by omega : (0 : ℤ) + 1 = 1) U.a.1 (connectingHom U))
        (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 T.b.1) =
      A.comp (by omega : (0 : ℤ) + 1 = 1) U.a.1
        (A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom T) T.b.1) := by
    calc
      _ = A.comp (by omega : (0 : ℤ) + 1 = 1) U.a.1
          (A.comp (by omega : (1 : ℤ) + 0 = 1) (connectingHom U)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 T.b.1)) :=
        (A.assoc (l := 0) (m := 1) (n := 0) (p := 1) (q := 1) (r := 1)
          (by omega) (by omega) (by omega) (by omega) U.a.1
          (connectingHom U)
          (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 T.b.1)).symm
      _ = _ := congrArg (fun t => A.comp (by omega : (0 : ℤ) + 1 = 1) U.a.1 t) hδb
  simp [A.d_add, A.leibniz, U.a.2, q.2, T.b.2, d_projection T,
    ← comp_connectingHom U, comp_neg_right, hterm]

private theorem split_map_inverse {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} {x y y' z z' : A.Obj}
    (T : GradedSplitShortExact (A := A) x y z)
    (U : GradedSplitShortExact (A := A) x y' z')
    (q : A.Hom z z' 0) (r : A.Hom z' z 0)
    (hqr : A.comp (by omega : (0 : ℤ) + 0 = 0) r q = A.id z) :
    A.comp (by omega : (0 : ℤ) + 0 = 0)
      (A.comp (by omega : (0 : ℤ) + 0 = 0) T.a.1 U.π +
        A.comp (by omega : (0 : ℤ) + 0 = 0) T.s
          (A.comp (by omega : (0 : ℤ) + 0 = 0) r U.b.1))
      (A.comp (by omega : (0 : ℤ) + 0 = 0) U.a.1 T.π +
        A.comp (by omega : (0 : ℤ) + 0 = 0) U.s
          (A.comp (by omega : (0 : ℤ) + 0 = 0) q T.b.1)) = A.id y := by
  have hUb := comp_zero U
  simp only [A.comp_add_left, A.comp_add_right]
  rw [← comp_assoc_zero T.a.1 U.π _, comp_assoc_zero U.π U.a.1 T.π,
    U.π_a, A.id_comp]
  rw [← comp_assoc_zero T.a.1 U.π _, comp_assoc_zero U.π U.s _, U.π_s]
  rw [← comp_assoc_zero T.s _ _, ← comp_assoc_zero r U.b.1 _,
    comp_assoc_zero U.b.1 U.a.1 T.π, hUb]
  rw [← comp_assoc_zero T.s _ _, ← comp_assoc_zero r U.b.1 _,
    comp_assoc_zero U.b.1 U.s _, U.b_s, A.id_comp,
    comp_assoc_zero r q T.b.1, hqr, A.id_comp]
  simpa using T.a_π_add_s_b


/-- The middle term of an admissible short exact sequence is homotopy equivalent
to the cone of the sequence's desuspended connecting map, compatibly with the
inclusion and the projection. -/
private theorem exists_cone_identification (hS : S.shift.RoundTripCoherent)
    {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    ∃ (u : A.Cocycle y (S.cone (S.shift.shiftedConnecting E))) (v : A.Cocycle (S.cone
      (S.shift.shiftedConnecting E)) y)
      (q : A.Cocycle z ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) (qinv :
        A.Cocycle ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z)) z),
      A.compCocycle v u = ⟨A.id y, A.d_id y⟩ ∧
      A.compCocycle u v = ⟨A.id (S.cone (S.shift.shiftedConnecting E)), A.d_id (S.cone
        (S.shift.shiftedConnecting E))⟩ ∧
      A.compCocycle qinv q = ⟨A.id z, A.d_id z⟩ ∧
      A.compCocycle q qinv = ⟨A.id ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj
        z)), A.d_id ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))⟩ ∧
      A.compCocycle v (S.coneSequence (S.shift.shiftedConnecting E)).a = E.a ∧
      A.compCocycle E.b v = A.compCocycle qinv (S.coneSequence (S.shift.shiftedConnecting
        E)).b ∧
      (S.shift.shiftFunctor 1).mapCocycle (S.shift.shiftedConnecting E) = A.compCocycle
        (S.shift.connectingCocycle E) qinv := by
  classical
  let : Category A.Obj := instCategoryComp A
  let : Category A.Comp := instCategoryComp A
  let Sh := S.shift
  let w := (Sh.shiftFunctor (-1)).obj z
  let z₁ := (Sh.shiftFunctor 1).obj w
  let q : A.Cocycle z z₁ := (Sh.reshiftIso z).inv
  let qinv : A.Cocycle z₁ z := (Sh.reshiftIso z).hom
  let f : A.Cocycle w x := Sh.shiftedConnecting E
  let g := Sh.connectingCocycle E
  let F := S.coneSequence f
  let δ := connectingHom E
  let δ' := connectingHom F
  let FPlus := (Sh.shiftFunctor 1).onComp
  let m : (show A.Comp from z₁) ⟶
      (show A.Comp from (Sh.shiftFunctor 1).obj x) := FPlus.map f
  have hm' : m = qinv ≫ (g : (show A.Comp from z) ⟶
      (show A.Comp from (Sh.shiftFunctor 1).obj x)) :=
    Sh.shift_shiftedConnecting hS E
  have hcat : q ≫ m = (g : (show A.Comp from z) ⟶
      (show A.Comp from (Sh.shiftFunctor 1).obj x)) := by
    have hqq : q ≫ qinv = (𝟙 (show A.Comp from z)) := (Sh.reshiftIso z).inv_hom_id
    calc
      q ≫ m = q ≫ (qinv ≫ g) := congrArg (fun t => q ≫ t) hm'
      _ = (q ≫ qinv) ≫ g :=
        (Category.assoc (self := (inferInstance : Category A.Comp))
          (q : (show A.Comp from z) ⟶ (show A.Comp from z₁))
          (qinv : (show A.Comp from z₁) ⟶ (show A.Comp from z))
          (g : (show A.Comp from z) ⟶ (show A.Comp from (Sh.shiftFunctor 1).obj x))).symm
      _ = (𝟙 (show A.Comp from z)) ≫ g := by rw [hqq]
      _ = g := by
        exact Category.id_comp (self := (inferInstance : Category A.Comp))
          (g : (show A.Comp from z) ⟶ (show A.Comp from (Sh.shiftFunctor 1).obj x))
  have hδ : A.comp (by omega : (1 : ℤ) + 0 = 1) δ' q.1 = δ := by
    apply (Sh.toShift 1 z x 0).injective
    have hcomp := Sh.toShift_comp_right (n := 1) (x := z) (y := z₁)
      (z := x) (l := 0) (m := 0) δ' q.1
    have hcomp' : (Sh.toShift 1 z x 0)
        (A.comp (by omega : (1 : ℤ) + 0 = 1) δ' q.1) =
        A.comp (by omega : (0 : ℤ) + 0 = 0) ((Sh.toShift 1 z₁ x 0) δ') q.1 := by
      simpa using hcomp
    rw [hcomp']
    show A.comp (by omega : (0 : ℤ) + 0 = 0)
        ((Sh.toShift 1 z₁ x 0) δ') q.1 = (Sh.toShift 1 z x 0) δ
    rw [show (Sh.toShift 1 z₁ x 0) δ' =
        (Sh.shiftFunctor 1).map f.1 by
          exact congrArg Subtype.val (S.cone_connecting f)]
    show A.comp (by omega : (0 : ℤ) + 0 = 0)
        ((Sh.shiftFunctor 1).map f.1) q.1 =
      (Sh.toShift 1 z x 0) δ
    have hval := congrArg (fun h : (show A.Comp from z) ⟶
      (show A.Comp from (Sh.shiftFunctor 1).obj x) => h.1) hcat
    change A.comp (by omega : (0 : ℤ) + 0 = 0)
        ((Sh.shiftFunctor 1).map f.1) q.1 =
      (Sh.toShift 1 z x 0) δ at hval
    simpa [g, ShiftAxiomBIso.connectingCocycle] using hval
  let uVal : A.Hom y (S.cone f) 0 :=
      A.comp (by omega : (0 : ℤ) + 0 = 0) F.a.1 E.π +
      A.comp (by omega : (0 : ℤ) + 0 = 0) F.s
        (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1)
  have huClosed : A.d uVal = 0 := split_map_closed E F q hδ
  let u : A.Cocycle y (S.cone f) := ⟨uVal, huClosed⟩
  have hqinvq : A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 qinv.1 = A.id z₁ :=
    congrArg Subtype.val (Sh.reshiftIso z).hom_inv_id
  have hδinv : A.comp (by omega : (1 : ℤ) + 0 = 1) δ qinv.1 = δ' := by
    calc
      _ = A.comp (by omega : (1 : ℤ) + 0 = 1) δ'
          (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 qinv.1) := by
            rw [← hδ]
            exact (A.assoc (l := 1) (m := 0) (n := 0) (p := 0) (q := 1) (r := 1)
              (by omega) (by omega) (by omega) (by omega) δ' q.1 qinv.1).symm
      _ = _ := by rw [hqinvq, A.comp_id]
  let vVal : A.Hom (S.cone f) y 0 :=
    A.comp (by omega : (0 : ℤ) + 0 = 0) E.a.1 F.π +
      A.comp (by omega : (0 : ℤ) + 0 = 0) E.s
        (A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 F.b.1)
  have hvClosed : A.d vVal = 0 := split_map_closed F E qinv hδinv
  let v : A.Cocycle (S.cone f) y := ⟨vVal, hvClosed⟩
  have hqqRaw : A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 q.1 = A.id z :=
    congrArg Subtype.val (Sh.reshiftIso z).inv_hom_id
  have hEba := comp_zero E
  have hFba := comp_zero F
  have hvuRaw : A.comp (by omega : (0 : ℤ) + 0 = 0) vVal uVal = A.id y :=
    split_map_inverse E F q.1 qinv.1 hqqRaw
  have huvRaw : A.comp (by omega : (0 : ℤ) + 0 = 0) uVal vVal = A.id (S.cone f) :=
    split_map_inverse F E qinv.1 q.1 hqinvq
  have hUA : A.comp (by omega : (0 : ℤ) + 0 = 0) uVal E.a.1 = F.a.1 := by
    dsimp [uVal]
    rw [A.comp_add_left, ← comp_assoc_zero F.a.1 E.π E.a.1, E.π_a, A.comp_id,
      comp_assoc_zero F.s q.1 E.b.1,
      ← comp_assoc_zero (A.comp (by omega : (0 : ℤ) + 0 = 0) F.s q.1) E.b.1 E.a.1,
      ← comp_assoc_zero F.s q.1 _, hEba]
    simp
  have hUB : A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 uVal =
      A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1 := by
    dsimp [uVal]
    rw [A.comp_add_right]
    have h1 : A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) F.a.1 E.π) = 0 := by
      calc
        _ = A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 F.a.1) E.π :=
          comp_assoc_zero F.b.1 F.a.1 E.π
        _ = 0 := by rw [hFba]; simp
    have h2 : A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1
        (A.comp (by omega : (0 : ℤ) + 0 = 0) F.s
          (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1)) =
        A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1 := by
      calc
        _ = A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 F.s)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1) :=
          comp_assoc_zero F.b.1 F.s (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1)
        _ = _ := by rw [F.b_s, A.id_comp]
    rw [h1, h2]
    simp
  have htermUB : A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
      (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 uVal) = E.b.1 := by
    calc
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
          (A.comp (by omega : (0 : ℤ) + 0 = 0) q.1 E.b.1) := congrArg
            (fun t => A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 t) hUB
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0)
          (A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 q.1) E.b.1 :=
        comp_assoc_zero qinv.1 q.1 E.b.1
      _ = _ := by rw [hqqRaw, A.id_comp]
  have hva : A.comp (by omega : (0 : ℤ) + 0 = 0) vVal F.a.1 = E.a.1 := by
    calc A.comp (by omega : (0 : ℤ) + 0 = 0) vVal F.a.1
        = A.comp (by omega : (0 : ℤ) + 0 = 0) vVal
            (A.comp (by omega : (0 : ℤ) + 0 = 0) uVal E.a.1) := by rw [hUA]
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) vVal uVal) E.a.1 :=
          comp_assoc_zero vVal uVal E.a.1
      _ = E.a.1 := by rw [hvuRaw, A.id_comp]
  have hvb : A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 vVal =
      A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 F.b.1 := by
    calc A.comp (by omega : (0 : ℤ) + 0 = 0) E.b.1 vVal
        = A.comp (by omega : (0 : ℤ) + 0 = 0)
            (A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
              (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 uVal)) vVal := by
          rw [htermUB]
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
            (A.comp (by omega : (0 : ℤ) + 0 = 0)
              (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 uVal) vVal) :=
          (comp_assoc_zero qinv.1
            (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1 uVal) vVal).symm
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
            (A.comp (by omega : (0 : ℤ) + 0 = 0) F.b.1
              (A.comp (by omega : (0 : ℤ) + 0 = 0) uVal vVal)) := by
          rw [comp_assoc_zero F.b.1 uVal vVal]
      _ = A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1 F.b.1 := by
          rw [huvRaw, A.comp_id]
  exact ⟨u, v, q, qinv, Subtype.ext hvuRaw, Subtype.ext huvRaw,
    Subtype.ext hqqRaw, Subtype.ext hqinvq, Subtype.ext hva, Subtype.ext hvb, hm'⟩

/-- The rotation of the cone triangle on the desuspended connecting map of an
admissible short exact sequence is isomorphic to the triangle of that sequence. -/
private theorem rotate_negativeCone_iso_associated (hS : S.shift.RoundTripCoherent)
    {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasShift A.K ℤ := S.shift.kShift
    Nonempty
      ((ConeSituationIso.negativeConeTriangle S
          (S.shift.shiftedConnecting E)).rotate ≅
        S.shift.associatedKTriangle E) := by
  let : Preadditive A.K := homotopyPreadditive A
  let : HasShift A.K ℤ := S.shift.kShift
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor A.K n).Additive :=
    fun n => homotopyShiftAdditiveIso A S n
  obtain ⟨u, v, q, qinv, hvu, huv, hqq, hqq', hva, hvb, hmf⟩ :=
    exists_cone_identification A S hS E
  have hw : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj (show A.K from ((S.shift.shiftFunctor
    (-1)).obj z)) = (show A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj
    z))) :=
    congrArg (fun G : A.K ⥤ A.K => G.obj ((S.shift.shiftFunctor (-1)).obj z))
      (S.shift.kShift_functor 1)
  have hx1 : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj (show A.K from x) = (show A.K from
    ((S.shift.shiftFunctor 1).obj x)) :=
    congrArg (fun G : A.K ⥤ A.K => G.obj x) (S.shift.kShift_functor 1)
  let ku : (show A.K from y) ⟶ (show A.K from (S.cone (S.shift.shiftedConnecting E))) :=
    Quotient.mk (A.homotopySetoid y (S.cone (S.shift.shiftedConnecting E))) u
  let kv : (show A.K from (S.cone (S.shift.shiftedConnecting E))) ⟶ (show A.K from y) :=
    Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) y) v
  let kq : (show A.K from z) ⟶ (show A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor
    (-1)).obj z))) := Quotient.mk (A.homotopySetoid z ((S.shift.shiftFunctor 1).obj
    ((S.shift.shiftFunctor (-1)).obj z))) q
  let kqinv : (show A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) ⟶
    (show A.K from z) :=
    Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))
      z) qinv
  let kEa : (show A.K from x) ⟶ (show A.K from y) := Quotient.mk (A.homotopySetoid x y) E.a
  let kEb : (show A.K from y) ⟶ (show A.K from z) := Quotient.mk (A.homotopySetoid y z) E.b
  let kFa : (show A.K from x) ⟶ (show A.K from (S.cone (S.shift.shiftedConnecting E))) :=
    Quotient.mk (A.homotopySetoid x (S.cone (S.shift.shiftedConnecting E)))
      (S.coneSequence (S.shift.shiftedConnecting E)).a
  let kFb : (show A.K from (S.cone (S.shift.shiftedConnecting E))) ⟶ (show A.K from
    ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) :=
    Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E))
      ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) (S.coneSequence
      (S.shift.shiftedConnecting E)).b
  let kg : (show A.K from z) ⟶ (show A.K from ((S.shift.shiftFunctor 1).obj x)) := Quotient.mk
    (A.homotopySetoid z ((S.shift.shiftFunctor 1).obj x)) (S.shift.connectingCocycle E)
  let kf : (show A.K from ((S.shift.shiftFunctor (-1)).obj z)) ⟶ (show A.K from x) := Quotient.mk
    (A.homotopySetoid ((S.shift.shiftFunctor (-1)).obj z) x) (S.shift.shiftedConnecting E)
  let kmf : (show A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) ⟶
    (show A.K from ((S.shift.shiftFunctor 1).obj x)) :=
    Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))
      ((S.shift.shiftFunctor 1).obj x))
      ((S.shift.shiftFunctor 1).mapCocycle (S.shift.shiftedConnecting E))
  have hkvu : kv ≫ ku = 𝟙 (show A.K from (S.cone (S.shift.shiftedConnecting E))) := by
    show Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) (S.cone
      (S.shift.shiftedConnecting E))) (A.compCocycle u v) =
      Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) (S.cone
        (S.shift.shiftedConnecting E))) ⟨A.id (S.cone (S.shift.shiftedConnecting
        E)), A.d_id (S.cone (S.shift.shiftedConnecting E))⟩
    rw [huv]
  have hkuv : ku ≫ kv = 𝟙 (show A.K from y) := by
    show Quotient.mk (A.homotopySetoid y y) (A.compCocycle v u) =
      Quotient.mk (A.homotopySetoid y y) ⟨A.id y, A.d_id y⟩
    rw [hvu]
  have hkqq : kq ≫ kqinv = 𝟙 (show A.K from z) := by
    show Quotient.mk (A.homotopySetoid z z) (A.compCocycle qinv q) =
      Quotient.mk (A.homotopySetoid z z) ⟨A.id z, A.d_id z⟩
    rw [hqq]
  have hkqq' : kqinv ≫ kq = 𝟙 (show A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor
    (-1)).obj z))) := by
    show Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor
      (-1)).obj z)) ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z)))
      (A.compCocycle q qinv) =
      Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj
        z)) ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))) ⟨A.id
        ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z)), A.d_id
        ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))⟩
    rw [hqq']
  have hkva : kFa ≫ kv = kEa := by
    show Quotient.mk (A.homotopySetoid x y) (A.compCocycle v (S.coneSequence
      (S.shift.shiftedConnecting E)).a) =
      Quotient.mk (A.homotopySetoid x y) E.a
    rw [hva]
  have hkvb : kv ≫ kEb = kFb ≫ kqinv := by
    show Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) z)
      (A.compCocycle E.b v) =
      Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) z)
        (A.compCocycle qinv (S.coneSequence (S.shift.shiftedConnecting E)).b)
    rw [hvb]
  have hkmf : kqinv ≫ kg = kmf := by
    show Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor
      (-1)).obj z)) ((S.shift.shiftFunctor 1).obj x))
        (A.compCocycle (S.shift.connectingCocycle E) qinv) =
      Quotient.mk (A.homotopySetoid ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj
        z)) ((S.shift.shiftFunctor 1).obj x))
        ((S.shift.shiftFunctor 1).mapCocycle (S.shift.shiftedConnecting E))
    rw [hmf]
  let i₁ : (show A.K from x) ≅ (show A.K from x) :=
    { hom := -(𝟙 (show A.K from x))
      inv := -(𝟙 (show A.K from x))
      hom_inv_id := by rw [Preadditive.neg_comp_neg, Category.id_comp]
      inv_hom_id := by rw [Preadditive.neg_comp_neg, Category.id_comp] }
  let i₂ : (show A.K from (S.cone (S.shift.shiftedConnecting E))) ≅ (show A.K from y) :=
    { hom := -kv
      inv := -ku
      hom_inv_id := by rw [neg_comp, comp_neg, neg_neg]; exact hkvu
      inv_hom_id := by rw [neg_comp, comp_neg, neg_neg]; exact hkuv }
  let i₃ : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj (show A.K from ((S.shift.shiftFunctor
    (-1)).obj z)) ≅ (show A.K from z) :=
    { hom := eqToHom hw ≫ kqinv
      inv := kq ≫ eqToHom hw.symm
      hom_inv_id := by
        rw [Category.assoc, ← Category.assoc kqinv kq (eqToHom hw.symm), hkqq',
          Category.id_comp, eqToHom_trans, eqToHom_refl]
      inv_hom_id := by
        rw [Category.assoc,
          ← Category.assoc (eqToHom hw.symm) (eqToHom hw) kqinv,
          eqToHom_trans, eqToHom_refl, Category.id_comp, hkqq] }
  refine ⟨Pretriangulated.Triangle.isoMk _ _ i₁ i₂ i₃ ?_ ?_ ?_⟩
  · show kFa ≫ (-kv) = (-(𝟙 (show A.K from x))) ≫ kEa
    rw [comp_neg, neg_comp, Category.id_comp, hkva]
  · have hcancel : ∀ m : (show A.K from (S.cone (S.shift.shiftedConnecting E))) ⟶ (show
      A.K from ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z))),
        (m ≫ eqToHom hw.symm) ≫ (eqToHom hw ≫ kqinv) = m ≫ kqinv := by
      intro m
      rw [Category.assoc,
        ← Category.assoc (eqToHom hw.symm) (eqToHom hw) kqinv,
        eqToHom_trans, eqToHom_refl, Category.id_comp]
    have hneg : A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
        (-((S.coneSequence (S.shift.shiftedConnecting E)).b.1)) =
        -A.comp (by omega : (0 : ℤ) + 0 = 0) qinv.1
          ((S.coneSequence (S.shift.shiftedConnecting E)).b.1) :=
      by simpa using (A.comp_sub_right (by omega : (0 : ℤ) + 0 = 0) qinv.1
        (0 : A.Hom _ _ 0) ((S.coneSequence
          (S.shift.shiftedConnecting E)).b.1))
    have h1 : A.compCocycle qinv (-((S.coneSequence (S.shift.shiftedConnecting E)).b)) =
        -(A.compCocycle qinv ((S.coneSequence (S.shift.shiftedConnecting E)).b)) :=
          Subtype.ext hneg
    show ((Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E))
      ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z)))
        (-((S.coneSequence (S.shift.shiftedConnecting E)).b) : A.Cocycle (S.cone
          (S.shift.shiftedConnecting E)) ((S.shift.shiftFunctor 1).obj
          ((S.shift.shiftFunctor (-1)).obj z))) :
          (show A.K from (S.cone (S.shift.shiftedConnecting E))) ⟶ (show A.K from
            ((S.shift.shiftFunctor 1).obj ((S.shift.shiftFunctor (-1)).obj z)))) ≫ eqToHom hw.symm)
            ≫
        (eqToHom hw ≫ kqinv) = (-kv) ≫ kEb
    rw [hcancel, neg_comp, hkvb]
    exact Eq.trans
      (congrArg (Quotient.mk (A.homotopySetoid (S.cone (S.shift.shiftedConnecting E)) z))
        h1)
      (homotopyClass_mk_neg A (S.cone (S.shift.shiftedConnecting E)) z (A.compCocycle qinv
        ((S.coneSequence (S.shift.shiftedConnecting E)).b)))
  · have hi1 : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map (-(𝟙 (show A.K from x))) = -(𝟙
      ((CategoryTheory.shiftFunctor A.K (1 : ℤ)).obj (show A.K from x))) := by
      rw [Functor.map_neg, (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map_id]
    have hshiftf : (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map kf = eqToHom hw ≫ kmf ≫ eqToHom
      hx1.symm := by
      rw [Functor.congr_hom (S.shift.kShift_functor (1 : ℤ)) kf]
      rfl
    show (-((CategoryTheory.shiftFunctor A.K (1 : ℤ)).map kf)) ≫
        (CategoryTheory.shiftFunctor A.K (1 : ℤ)).map (-(𝟙 (show A.K from x))) =
      (eqToHom hw ≫ kqinv) ≫ kg ≫ eqToHom hx1.symm
    rw [hi1, comp_neg, neg_comp, neg_neg, Category.comp_id, hshiftf, ← hkmf,
      Category.assoc kqinv kg (eqToHom hx1.symm),
      Category.assoc (eqToHom hw) kqinv (kg ≫ eqToHom hx1.symm)]

private theorem invRotate_associated_distinguished (hS : S.shift.RoundTripCoherent)
    {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasShift A.K ℤ := S.shift.kShift
    IsDistinguishedTriangleIso A S
      (S.shift.associatedKTriangle E).invRotate := by
  let : Preadditive A.K := homotopyPreadditive A
  let : HasShift A.K ℤ := S.shift.kShift
  let : ∀ n : ℤ, (CategoryTheory.shiftFunctor A.K n).Additive :=
    fun n => homotopyShiftAdditiveIso A S n
  obtain ⟨e⟩ := rotate_negativeCone_iso_associated A S hS E
  obtain ⟨x', y', z', E', ⟨k⟩⟩ :=
    negativeCone_distinguished A S (S.shift.shiftedConnecting E)
  let m : (Pretriangulated.rotate A.K).obj
      (S.shift.associatedKTriangle E') ≅
      S.shift.associatedKTriangle E :=
    ((Pretriangulated.rotate A.K).mapIso k).symm.trans e
  exact ⟨x', y', z', E', ⟨((Pretriangulated.invRotate A.K).mapIso m.symm).trans
    ((Pretriangulated.rotCompInvRot (C := A.K)).app (S.shift.associatedKTriangle E')).symm⟩⟩

/-- A pretriangulated structure on the homotopy category, bundled with the identification of
its distinguished triangles with those of admissible short exact sequences. -/
@[no_expose, sga "4½ Etat_0 1.2.2" "more general"]
public noncomputable def homotopyPretriangulatedBundledIso (hS : S.shift.RoundTripCoherent) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A S
    letI : HasShift A.K ℤ := S.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
    { P : Pretriangulated A.K //
      P.distinguishedTriangles = {U | IsDistinguishedTriangleIso A S U} } := by
  letI : Preadditive A.K := homotopyPreadditive A
  letI : Category A.K := instCategoryK A
  letI : HasZeroObject A.K := homotopyHasZeroObjectIso A S
  letI : HasShift A.K ℤ := S.shift.kShift
  letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
  refine
    ⟨{ distinguishedTriangles := {U | IsDistinguishedTriangleIso A S U}
       isomorphic_distinguished := ?_
       contractible_distinguished := ?_
       distinguished_cocone_triangle := ?_
       rotate_distinguished_triangle := ?_
       complete_distinguished_triangle_morphism := ?_ }, rfl⟩
  · intro T₁ hT₁ T₂ e
    rcases hT₁ with ⟨x, y, z, E, ⟨i⟩⟩
    exact ⟨x, y, z, E, ⟨e.trans i⟩⟩
  · intro X
    let E := zeroSplitShortExact A S X
    let : Category A.Obj := instCategoryK A
    let : Preadditive A.Obj := homotopyPreadditive A
    let : HasZeroObject A.Obj := homotopyHasZeroObjectIso A S
    have hz : IsZero (S.directSum.zero : A.K) := homotopyZeroIsZero A S (homotopyPreadditive A)
    refine ⟨X, X, S.directSum.zero, E, ⟨?_⟩⟩
    refine Pretriangulated.Triangle.isoMk (Pretriangulated.contractibleTriangle X)
      (S.shift.associatedKTriangle E)
      (Iso.refl _) (Iso.refl _)
      hz.isoZero.symm ?_ ?_ ?_
    · rfl
    · exact hz.eq_of_tgt _ _
    · exact IsZero.eq_of_src (isZero_zero A.K) _ _
  · intro X Y f
    obtain ⟨f', rfl⟩ := Quotient.exists_rep f
    have hmem : IsDistinguishedTriangleIso A S (ConeSituationIso.negativeConeTriangle S f') :=
      negativeCone_distinguished (A := A) (S := S) f'
    refine ⟨S.cone f', (ConeSituationIso.negativeConeTriangle S f').mor₂,
      (ConeSituationIso.negativeConeTriangle S f').mor₃, ?_⟩
    change IsDistinguishedTriangleIso A S (ConeSituationIso.negativeConeTriangle S f')
    exact hmem
  · intro T
    change IsDistinguishedTriangleIso A S T ↔
      IsDistinguishedTriangleIso A S T.rotate
    constructor
    · intro hT
      rcases hT with ⟨x, y, z, E, ⟨i⟩⟩
      let : Category A.K := instCategoryK A
      let : Category A.Obj := instCategoryK A
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        ConeSituationIso.coneTriangleIsoOfShortExact S E
      have hφ : IsIso φ := Pretriangulated.Triangle.isIso_of_isIsos φ
        (by rw [hφ₁]; change IsIso (𝟙 (x : A.K)); infer_instance)
        (by rw [hφ₂]; change IsIso (𝟙 (y : A.K)); infer_instance) hφ₃
      let j : S.shift.associatedKTriangle E ≅
          ConeSituationIso.negativeConeTriangle S E.a := (asIso φ).symm
      have hn := negativeCone_rotate_distinguished (A := A) (S := S) E.a
      have hi : T.rotate ≅ (ConeSituationIso.negativeConeTriangle S E.a).rotate :=
        ((Pretriangulated.rotate A.K).mapIso i).trans
          ((Pretriangulated.rotate A.K).mapIso j)
      rcases hn with ⟨x', y', z', E', ⟨k⟩⟩
      exact ⟨x', y', z', E', ⟨hi.trans k⟩⟩
    · intro hT
      rcases hT with ⟨x, y, z, E, ⟨i⟩⟩
      have hU := invRotate_associated_distinguished (A := A) (S := S) hS E
      let j : T ≅ (S.shift.associatedKTriangle E).invRotate :=
        (Pretriangulated.rotCompInvRot (C := A.K)).app T |>.trans
          ((Pretriangulated.invRotate A.K).mapIso i)
      rcases hU with ⟨x', y', z', E', ⟨k⟩⟩
      exact ⟨x', y', z', E', ⟨j.trans k⟩⟩
  · intro T₁ T₂ h₁ h₂ a b h
    rcases h₁ with ⟨x₁, y₁, z₁, E₁, ⟨i₁⟩⟩
    rcases h₂ with ⟨x₂, y₂, z₂, E₂, ⟨i₂⟩⟩
    let U₁ := S.shift.associatedKTriangle E₁
    let U₂ := S.shift.associatedKTriangle E₂
    let aK : A.HomotopyClass x₁ x₂ := (i₁.inv.hom₁ ≫ a) ≫ i₂.hom.hom₁
    let bK : A.HomotopyClass y₁ y₂ := (i₁.inv.hom₂ ≫ b) ≫ i₂.hom.hom₂
    have hi₁ : U₁.mor₁ ≫ i₁.inv.hom₂ = i₁.inv.hom₁ ≫ T₁.mor₁ := by
      simpa only [U₁] using i₁.inv.comm₁
    have hi₂ : T₂.mor₁ ≫ i₂.hom.hom₂ = i₂.hom.hom₁ ≫ U₂.mor₁ := by
      simpa only [U₂] using i₂.hom.comm₁
    have habK : A.compK bK U₁.mor₁ = A.compK U₂.mor₁ aK := by
      change U₁.mor₁ ≫ bK = aK ≫ U₂.mor₁
      dsimp [aK, bK]
      calc
        U₁.mor₁ ≫ ((i₁.inv.hom₂ ≫ b) ≫ i₂.hom.hom₂) =
            ((U₁.mor₁ ≫ i₁.inv.hom₂) ≫ b) ≫ i₂.hom.hom₂ := by
          exact (Category.assoc U₁.mor₁ (i₁.inv.hom₂ ≫ b) i₂.hom.hom₂).symm.trans
            (congrArg (fun q => q ≫ i₂.hom.hom₂)
              (Category.assoc U₁.mor₁ i₁.inv.hom₂ b).symm)
        _ = ((i₁.inv.hom₁ ≫ T₁.mor₁) ≫ b) ≫ i₂.hom.hom₂ := by rw [hi₁]
        _ = ((i₁.inv.hom₁ ≫ a) ≫ T₂.mor₁) ≫ i₂.hom.hom₂ := by
          calc
            ((i₁.inv.hom₁ ≫ T₁.mor₁) ≫ b) ≫ i₂.hom.hom₂ =
                (i₁.inv.hom₁ ≫ (T₁.mor₁ ≫ b)) ≫ i₂.hom.hom₂ := by
                  simp only [Category.assoc]
            _ = (i₁.inv.hom₁ ≫ (a ≫ T₂.mor₁)) ≫ i₂.hom.hom₂ := by rw [h]
            _ = ((i₁.inv.hom₁ ≫ a) ≫ T₂.mor₁) ≫ i₂.hom.hom₂ := by
                  simp only [Category.assoc]
        _ = ((i₁.inv.hom₁ ≫ a) ≫ i₂.hom.hom₁) ≫ U₂.mor₁ := by
          calc
            ((i₁.inv.hom₁ ≫ a) ≫ T₂.mor₁) ≫ i₂.hom.hom₂ =
                (i₁.inv.hom₁ ≫ a) ≫ (T₂.mor₁ ≫ i₂.hom.hom₂) := by
                  rw [Category.assoc]
            _ = (i₁.inv.hom₁ ≫ a) ≫ (i₂.hom.hom₁ ≫ U₂.mor₁) := by rw [hi₂]
            _ = ((i₁.inv.hom₁ ≫ a) ≫ i₂.hom.hom₁) ≫ U₂.mor₁ := by
                  rw [← Category.assoc]
    obtain ⟨a', ha'⟩ := Quotient.exists_rep aK
    obtain ⟨b', hb'⟩ := Quotient.exists_rep bK
    have hU₁ : U₁.mor₁ = Quotient.mk (A.homotopySetoid x₁ y₁) E₁.a := rfl
    have hU₂ : U₂.mor₁ = Quotient.mk (A.homotopySetoid x₂ y₂) E₂.a := rfl
    have hab : A.compK (Quotient.mk (A.homotopySetoid y₁ y₂) b')
        (Quotient.mk (A.homotopySetoid x₁ y₁) E₁.a) =
        A.compK (Quotient.mk (A.homotopySetoid x₂ y₂) E₂.a)
          (Quotient.mk (A.homotopySetoid x₁ x₂) a') := by
      rwa [← ha', ← hb', hU₁, hU₂] at habK
    obtain ⟨φ₁, hφ₁₁, hφ₁₂, hφ₁₃⟩ :=
      ConeSituationIso.coneTriangleIsoOfShortExact S E₁
    obtain ⟨φ₂, hφ₂₁, hφ₂₂, hφ₂₃⟩ :=
      ConeSituationIso.coneTriangleIsoOfShortExact S E₂
    have hφ₁ : IsIso φ₁ := by
      let : Category A.Obj := instCategoryK A
      exact Pretriangulated.Triangle.isIso_of_isIsos φ₁
        (by rw [hφ₁₁]; change IsIso (𝟙 (x₁ : A.K)); infer_instance)
        (by rw [hφ₁₂]; change IsIso (𝟙 (y₁ : A.K)); infer_instance) hφ₁₃
    have hφ₂ : IsIso φ₂ := by
      let : Category A.Obj := instCategoryK A
      exact Pretriangulated.Triangle.isIso_of_isIsos φ₂
        (by rw [hφ₂₁]; change IsIso (𝟙 (x₂ : A.K)); infer_instance)
        (by rw [hφ₂₂]; change IsIso (𝟙 (y₂ : A.K)); infer_instance) hφ₂₃
    let j₁ : ConeSituationIso.negativeConeTriangle S E₁.a ≅ U₁ := by
      refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (asIso φ₁.hom₃) ?_ ?_ ?_
      · simpa [hφ₁₁, hφ₁₂] using φ₁.comm₁
      · have hc := φ₁.comm₂
        rw [hφ₁₂] at hc
        simpa only [U₁, asIso_hom, Iso.refl_hom, Category.id_comp] using hc
      · simpa [hφ₁₁] using φ₁.comm₃
    let j₂ : ConeSituationIso.negativeConeTriangle S E₂.a ≅ U₂ := by
      refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (asIso φ₂.hom₃) ?_ ?_ ?_
      · simpa [hφ₂₁, hφ₂₂] using φ₂.comm₁
      · have hc := φ₂.comm₂
        rw [hφ₂₂] at hc
        simpa only [U₂, asIso_hom, Iso.refl_hom, Category.id_comp] using hc
      · simpa [hφ₂₁] using φ₂.comm₃
    obtain ⟨c, hc₂, hc₃⟩ := ConeSituationIso.exists_coneTriangleMorphism S
      E₁.a E₂.a a' b' hab
    let k₁ := Quotient.mk (A.homotopySetoid x₁ x₂) a'
    let k₂ := Quotient.mk (A.homotopySetoid y₁ y₂) b'
    let k₃ := Quotient.mk (A.homotopySetoid (S.cone E₁.a) (S.cone E₂.a)) c
    let γ : ConeSituationIso.negativeConeTriangle S E₁.a ⟶
        ConeSituationIso.negativeConeTriangle S E₂.a := by
      refine Pretriangulated.Triangle.homMk _ _ k₁ k₂ k₃ ?_ ?_ ?_
      · change A.compK (Quotient.mk _ b') (Quotient.mk _ E₁.a) =
          A.compK (Quotient.mk _ E₂.a) (Quotient.mk _ a')
        exact hab
      · change A.compK k₃ (Quotient.mk _ (S.coneSequence E₁.a).a) =
          A.compK (Quotient.mk _ (S.coneSequence E₂.a).a) k₂
        exact hc₂
      · dsimp [ConeSituationIso.negativeConeTriangle, k₁, k₃]
        let h₁ : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from x₁) =
            (S.shift.shiftFunctor (1 : ℤ)).onK.obj (show A.K from x₁) :=
          congrArg (fun F : A.K ⥤ A.K => F.obj x₁)
            (S.shift.kShift_functor (1 : ℤ))
        let h₂ : (shiftFunctor A.K (1 : ℤ)).obj (show A.K from x₂) =
            (S.shift.shiftFunctor (1 : ℤ)).onK.obj (show A.K from x₂) :=
          congrArg (fun F : A.K ⥤ A.K => F.obj x₂)
            (S.shift.kShift_functor (1 : ℤ))
        let d₁ : A.HomotopyClass (S.cone E₁.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₁) :=
          Quotient.mk _ (S.coneSequence E₁.a).b
        let d₂ : A.HomotopyClass (S.cone E₂.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₂) :=
          Quotient.mk _ (S.coneSequence E₂.a).b
        let G := (S.shift.shiftFunctor (1 : ℤ)).onK
        let : AddCommGroup (A.HomotopyClass (S.cone E₁.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₁)) :=
          homotopyClassAddCommGroup A (S.cone E₁.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₁)
        let : AddCommGroup (A.HomotopyClass (S.cone E₂.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₂)) :=
          homotopyClassAddCommGroup A (S.cone E₂.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₂)
        let : AddCommGroup (A.HomotopyClass (S.cone E₁.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₂)) :=
          homotopyClassAddCommGroup A (S.cone E₁.a)
            ((S.shift.shiftFunctor (1 : ℤ)).obj x₂)
        have hmap : eqToHom h₁.symm ≫ (shiftFunctor A.K (1 : ℤ)).map k₁ =
            G.map k₁ ≫ eqToHom h₂.symm := by
          rw [Functor.congr_hom (S.shift.kShift_functor (1 : ℤ)) k₁]
          simp [G]
        have hbase : k₃ ≫ d₂ = d₁ ≫ G.map k₁ := by
          change A.compK d₂ k₃ =
            A.compK (G.map k₁) d₁
          exact hc₃
        have hbaseNeg : (-d₁) ≫ G.map k₁ = k₃ ≫ (-d₂) := by
          let : AddCommGroup (A.HomotopyClass (S.cone E₁.a) (G.obj x₂)) :=
            homotopyClassAddCommGroup A _ _
          calc
            (-d₁) ≫ G.map k₁ = -(d₁ ≫ G.map k₁) := by
              exact neg_comp d₁ (G.map k₁)
            _ = -(k₃ ≫ d₂) := by rw [hbase.symm]
            _ = k₃ ≫ (-d₂) := by
              exact (Preadditive.comp_neg (C := A.K) k₃ d₂).symm
        change ((-d₁) ≫ eqToHom h₁.symm) ≫
            (shiftFunctor A.K (1 : ℤ)).map k₁ =
          k₃ ≫ ((-d₂) ≫ eqToHom h₂.symm)
        calc
          ((-d₁) ≫ eqToHom h₁.symm) ≫
              (shiftFunctor A.K (1 : ℤ)).map k₁ =
              (-d₁) ≫ (eqToHom h₁.symm ≫
                (shiftFunctor A.K (1 : ℤ)).map k₁) := by
                  exact Category.assoc _ _ _
          _ = (-d₁) ≫ (G.map k₁ ≫ eqToHom h₂.symm) := by rw [hmap]
          _ = ((-d₁) ≫ G.map k₁) ≫ eqToHom h₂.symm := by
                exact (Category.assoc _ _ _).symm
          _ =
              (k₃ ≫ (-d₂)) ≫ eqToHom h₂.symm := by rw [hbaseNeg]
          _ = k₃ ≫ ((-d₂) ≫ eqToHom h₂.symm) := by
                exact Category.assoc _ _ _
    let δ : U₁ ⟶ U₂ := j₁.inv ≫ γ ≫ j₂.hom
    let ε : T₁ ⟶ T₂ := i₁.hom ≫ δ ≫ i₂.inv
    refine ⟨ε.hom₃, ?_, ?_⟩
    · have hδ₂ : δ.hom₂ = bK := by
        let : Category A.Obj := instCategoryK A
        simp only [δ, j₁, j₂, γ, k₂, hb',
          Pretriangulated.Triangle.isoMk, Pretriangulated.Triangle.homMk]
        change (𝟙 y₁) ≫ bK ≫ (𝟙 y₂) = bK
        simp
      have he₂ : ε.hom₂ = b := by
        change i₁.hom.hom₂ ≫ δ.hom₂ ≫ i₂.inv.hom₂ = b
        rw [hδ₂]
        calc
          i₁.hom.hom₂ ≫ ((i₁.inv.hom₂ ≫ b) ≫ i₂.hom.hom₂) ≫ i₂.inv.hom₂ =
              ((i₁.hom.hom₂ ≫ i₁.inv.hom₂) ≫ b) ≫
                (i₂.hom.hom₂ ≫ i₂.inv.hom₂) := by
                  simp only [Category.assoc]
          _ = b := by simp
      rw [← he₂, ← ε.comm₂]
    · have hδ₁ : δ.hom₁ = aK := by
        let : Category A.Obj := instCategoryK A
        simp only [δ, j₁, j₂, γ, k₁, ha',
          Pretriangulated.Triangle.isoMk, Pretriangulated.Triangle.homMk]
        change (𝟙 x₁) ≫ aK ≫ (𝟙 x₂) = aK
        simp
      have he₁ : ε.hom₁ = a := by
        change i₁.hom.hom₁ ≫ δ.hom₁ ≫ i₂.inv.hom₁ = a
        rw [hδ₁]
        calc
          i₁.hom.hom₁ ≫ ((i₁.inv.hom₁ ≫ a) ≫ i₂.hom.hom₁) ≫ i₂.inv.hom₁ =
              ((i₁.hom.hom₁ ≫ i₁.inv.hom₁) ≫ a) ≫
                (i₂.hom.hom₁ ≫ i₂.inv.hom₁) := by
                  simp only [Category.assoc]
          _ = a := by simp
      rw [← he₁, ← ε.comm₃]

/-- The homotopy category with the triangles of admissible short exact sequences as its
distinguished triangles is pretriangulated. -/
@[instance_reducible, sga "4½ Etat_0 1.2.2" "partial"]
public noncomputable def homotopyPretriangulatedIso (hS : S.shift.RoundTripCoherent) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A S
    letI : HasShift A.K ℤ := S.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
    Pretriangulated A.K :=
  (homotopyPretriangulatedBundledIso A S hS).1

/-- The distinguished triangles of the pretriangulated structure on `K(A)` are exactly the
triangles isomorphic to that of an admissible short exact sequence. -/
@[sga "4½ Etat_0 1.2.2" "more general"]
public theorem distinguishedTriangles_homotopyPretriangulatedIso
    (hS : S.shift.RoundTripCoherent) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A S
    letI : HasShift A.K ℤ := S.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
    (homotopyPretriangulatedIso A S hS).distinguishedTriangles =
      {U | IsDistinguishedTriangleIso A S U} :=
  (homotopyPretriangulatedBundledIso A S hS).2

private lemma transport_across_iso {C : Type u} [Category.{v} C]
    {Y₁ Y₂ X₁ X₂ : C} (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂)
    (g : Y₁ ⟶ Y₂) (f : X₁ ⟶ X₂)
    (h : g ≫ e₂.hom = e₁.hom ≫ f) :
    f ≫ e₂.inv = e₁.inv ≫ g := by
  rw [e₂.comp_inv_eq, Category.assoc]; exact ((e₁.inv_comp_eq).2 h).symm

/-- The homotopy category of a differential graded category satisfying axioms (A), (B) and (C),
with the translation functors of axiom (B) and the triangles of admissible short exact sequences
as distinguished triangles, is a triangulated category. -/
@[sga "4 Vbis 2.5.1" "more general"]
public theorem homotopyCategory_isTriangulatedIso (hS : S.shift.RoundTripCoherent) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A S
    letI : HasShift A.K ℤ := S.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
    letI : Pretriangulated A.K := homotopyPretriangulatedIso A S hS
    IsTriangulated A.K := by
  let : Preadditive A.K := homotopyPreadditive A
  let : Category A.K := instCategoryK A
  let : HasZeroObject A.K := homotopyHasZeroObjectIso A S
  let : HasShift A.K ℤ := S.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A S n
  let : Pretriangulated A.K := homotopyPretriangulatedIso A S hS
  have hdist : Pretriangulated.distinguishedTriangles (C := A.K) =
      {U | IsDistinguishedTriangleIso A S U} :=
    distinguishedTriangles_homotopyPretriangulatedIso A S hS
  apply IsTriangulated.mk'
  intro X₁' X₂' X₃' u₁₂' u₂₃'
  obtain ⟨c₁₂, hc₁₂⟩ := Quotient.exists_rep u₁₂'
  obtain ⟨c₂₃, hc₂₃⟩ := Quotient.exists_rep u₂₃'
  let x : Fin 3 → A.Comp := ![X₁', X₂', X₃']
  let f : ∀ i : Fin 2, x i.castSucc ⟶ x i.succ :=
    fun i => Fin.cases c₁₂ (fun j => Fin.cases c₂₃ (fun k => Fin.elim0 k) j) i
  obtain ⟨y, g, p, hg, hp, hcomm⟩ := ConeSituationIso.exists_admissibleMono_sequence A S 2 x f
  have := hp (Fin.castSucc (0 : Fin 2))
  have := hp (Fin.succ (0 : Fin 2))
  have := hp (Fin.succ (1 : Fin 2))
  let e₁ : X₁' ≅ A.compToK.obj (y (Fin.castSucc (0 : Fin 2))) :=
    (asIso (A.compToK.map (p (Fin.castSucc (0 : Fin 2))))).symm
  let e₂ : X₂' ≅ A.compToK.obj (y (Fin.succ (0 : Fin 2))) :=
    (asIso (A.compToK.map (p (Fin.succ (0 : Fin 2))))).symm
  let e₃ : X₃' ≅ A.compToK.obj (y (Fin.succ (1 : Fin 2))) :=
    (asIso (A.compToK.map (p (Fin.succ (1 : Fin 2))))).symm
  obtain ⟨q₁, E₁, hE₁⟩ := hg ⟨0, by omega⟩
  obtain ⟨q₃, E₃, hE₃⟩ := hg ⟨1, by omega⟩
  have hcommK (i : Fin 2) : A.compToK.map (g i) ≫ A.compToK.map (p i.succ) =
      A.compToK.map (p i.castSucc) ≫ A.compToK.map (f i) := by
    simpa only [Functor.map_comp] using congrArg (fun k => A.compToK.map k) (hcomm i)
  obtain ⟨q₂, E₂, E₄, hcomp, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    admissibleMonomorphisms_octahedronIso S hS E₁ E₃
  let T₁ := S.shift.associatedKTriangle E₁
  let T₃ := S.shift.associatedKTriangle E₃
  have hT {a b c : A.Obj} (E : GradedSplitShortExact (A := A) a b c) :
      S.shift.associatedKTriangle E ∈ Pretriangulated.distinguishedTriangles (C := A.K) := by
    rw [hdist]; exact ⟨_, _, _, E, ⟨Iso.refl _⟩⟩
  let T₂ := S.shift.associatedKTriangle E₂
  let T₄ := S.shift.associatedKTriangle E₄
  have h₁₂' : u₁₂' ≫ e₂.hom = e₁.hom ≫ T₁.mor₁ := by
    show u₁₂' ≫ e₂.hom = e₁.hom ≫ Quotient.mk _ E₁.a
    rw [hE₁, ← hc₁₂]
    exact transport_across_iso e₁.symm e₂.symm (A.compToK.map (g 0))
      (A.compToK.map (f 0)) (hcommK 0)
  have h₂₃' : u₂₃' ≫ e₃.hom = e₂.hom ≫ T₃.mor₁ := by
    show u₂₃' ≫ e₃.hom = e₂.hom ≫ Quotient.mk _ E₃.a
    rw [hE₃, ← hc₂₃]
    exact transport_across_iso e₂.symm e₃.symm (A.compToK.map (g 1))
      (A.compToK.map (f 1)) (hcommK 1)
  refine ⟨T₁.obj₁, T₁.obj₂, T₃.obj₂, T₁.obj₃, T₃.obj₃, T₂.obj₃,
    T₁.mor₁, T₃.mor₁, e₁, e₂, e₃, h₁₂', h₂₃',
    T₁.mor₂, T₁.mor₃, hT E₁, T₃.mor₂, T₃.mor₃, hT E₃,
    T₂.mor₂, T₂.mor₃, ?_, ?_⟩
  · rw [show T₁.mor₁ ≫ T₃.mor₁ = T₂.mor₁ by simpa [T₁, T₃, T₂] using h₁]; exact hT E₂
  · refine ⟨⟨T₄.mor₁, T₄.mor₂, h₂, h₃, h₄, h₅, ?_⟩⟩
    have key : Pretriangulated.Triangle.mk T₄.mor₁ T₄.mor₂ (T₃.mor₃ ≫ T₁.mor₂⟦(1 : ℤ)⟧') =
        Pretriangulated.Triangle.mk T₄.mor₁ T₄.mor₂ T₄.mor₃ :=
      congrArg (Pretriangulated.Triangle.mk T₄.mor₁ T₄.mor₂) h₆.symm
    exact Set.mem_of_eq_of_mem key (hT E₄)

/-! ### The strict axiom (B)

A `DGCategory.ConeSituation` is a cone situation up to isomorphism
(`DGCategory.ConeSituation.toConeSituationIso`) whose round-trip coherence is automatic
(`DGCategory.ShiftAxiomB.roundTripCoherent`), so each declaration above has a strict form. -/

section Strict

variable (T : ConeSituation A)

include A T in
/-- The zero object of axiom (A) is a zero object of the homotopy category. -/
public theorem homotopyHasZeroObject : HasZeroObject A.K :=
  homotopyHasZeroObjectIso A T.toConeSituationIso

/-- Each translation functor of the homotopy category is additive. -/
@[sga "4½ Etat_0 1.2.2" "partial"]
public theorem homotopyShiftAdditive (n : ℤ) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasShift A.K ℤ := T.shift.kShift
    (shiftFunctor A.K n).Additive :=
  homotopyShiftAdditiveIso A T.toConeSituationIso n

/-- A triangle is distinguished if it is isomorphic to one obtained from an
admissible graded-split short exact sequence. -/
public def IsDistinguishedTriangle :
    letI : HasShift A.K ℤ := T.shift.kShift
    Pretriangulated.Triangle A.K → Prop := by
  letI : HasShift A.K ℤ := T.shift.kShift
  exact fun U => ∃ (x y z : A.Obj)
    (E : GradedSplitShortExact (A := A) x y z),
      Nonempty (U ≅ GradedSplitShortExact.associatedKTriangle T.shift E)

/-- The homotopy category with the triangles of admissible short exact sequences as its
distinguished triangles is pretriangulated. -/
@[instance_reducible,
  stacks 09QW "the pre-triangulated structure",
  sga "4½ Etat_0 1.2.2" "TR1, TR2, TR3"]
public noncomputable def homotopyPretriangulated :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A T
    letI : HasShift A.K ℤ := T.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A T n
    Pretriangulated A.K :=
  homotopyPretriangulatedIso A T.toConeSituationIso T.shift.roundTripCoherent

/-- The distinguished triangles of the pretriangulated structure on `K(A)` are exactly the
triangles isomorphic to that of an admissible short exact sequence. -/
@[stacks 09QW "its distinguished triangles", sga "4½ Etat_0 1.2.2" "more general"]
public theorem distinguishedTriangles_homotopyPretriangulated :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A T
    letI : HasShift A.K ℤ := T.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A T n
    (homotopyPretriangulated A T).distinguishedTriangles =
      {U | IsDistinguishedTriangle A T U} :=
  distinguishedTriangles_homotopyPretriangulatedIso A T.toConeSituationIso
    T.shift.roundTripCoherent

/-- The homotopy category of a differential graded category satisfying axioms (A), (B) and (C),
with the translation functors of axiom (B) and the triangles of admissible short exact sequences
as distinguished triangles, is a triangulated category. -/
@[stacks 09QY, sga "4½ Etat_0 1.2.2", sga "4 Vbis 2.5.1" "more general"]
public theorem homotopyCategory_isTriangulated :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A T
    letI : HasShift A.K ℤ := T.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A T n
    letI : Pretriangulated A.K := homotopyPretriangulated A T
    IsTriangulated A.K :=
  homotopyCategory_isTriangulatedIso A T.toConeSituationIso T.shift.roundTripCoherent

end Strict

end DGCategory
