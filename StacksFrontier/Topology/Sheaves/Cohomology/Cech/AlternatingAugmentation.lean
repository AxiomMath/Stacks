module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex

/-!
# The augmentation of the alternating Čech complex

Let `F` be an abelian presheaf on a space `X`, let `U` be an open subset and let
`V : I → Opens X` be a family of open subsets all contained in `U`. Restricting a section of
`F` over `U` to every member of the family gives a Čech cochain of degree zero, which is
alternating for trivial reasons and is killed by the Čech differential. The resulting map from
the sections over `U` to degree zero of the alternating Čech complex is the *augmentation*.

## Main definitions

* `Stacks.Cech.cechDegreeZeroRestriction`: restriction of a section over `U` to all members of
  the family, as an element of the degree-zero Čech cochain group.
* `Stacks.Cech.alternatingCechAugmentation`: the canonical augmentation of the alternating
  Čech complex.

## Main results

* `Stacks.Cech.cechDegreeZeroRestriction_isAlternating`: the restriction of a section is an
  alternating cochain.
* `Stacks.Cech.cechDegreeZeroRestriction_d` and
  `Stacks.Cech.alternatingCechAugmentation_d`: the augmentation is annihilated by the Čech
  differential, on cochains and as a morphism of complexes.

## Implementation notes

A degree-zero cochain is indexed by `Fin 1 → I`, so the alternating condition is vacuous: any
two indices of a one-element tuple agree, which both halves of `CechCochains.IsAlternating`
exploit. Only containment of every member of the family in `U` is needed; no covering
hypothesis occurs, and the member equal to `U` that makes the augmented complex contractible
is required only by the contractibility statement.

The augmenting object is taken in the universe of the cochain groups, which may be larger
than the universe of the values of `F`, hence the `ULift`.

The cochain-level operations are those of Tag 01FJ and the alternating complex is that of
Tag 01FH.

## References

* [Stacks Project, Tag 0G6T](https://stacks.math.columbia.edu/tag/0G6T)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Stacks.Cech

/-- Restriction of a section to every member of the family, in the explicit degree-zero
Čech cochain group. -/
def cechDegreeZeroRestriction (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    ULift.{v} (F.obj (op U) : Type w) →+ CechCochains.Cochain V F 0 :=
  AddMonoidHom.pi (fun i : Fin 1 → I ↦
    (CechCochains.restr F (by simpa [CechCochains.inter] using hV (i 0))).comp
      { toFun := ULift.down
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })

/-- The restriction of a section of `F` over `U` to the members of the family is an
alternating cochain: a degree-zero index tuple has a single entry, so no two of its indices
can differ. -/
lemma cechDegreeZeroRestriction_isAlternating (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U)
    (x : ULift.{v} (F.obj (op U) : Type w)) :
    CechCochains.IsAlternating V F (cechDegreeZeroRestriction X F V hV x) :=
  ⟨fun _ hσ ↦ (hσ fun a b _ ↦ Subsingleton.elim (α := Fin 1) a b).elim,
    fun _ a b hab ↦ (hab (Subsingleton.elim (α := Fin 1) a b)).elim⟩

/-- The Čech differential kills the restriction of a section over `U`: the two faces of a
degree-one index tuple both restrict that section along the same inclusion. -/
lemma cechDegreeZeroRestriction_d (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U)
    (x : ULift.{v} (F.obj (op U) : Type w)) :
    CechCochains.cechD V F 0 (cechDegreeZeroRestriction X F V hV x) = 0 := by
  classical
  funext τ
  show (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
      CechCochains.restr F (CechCochains.inter_le_omit V τ k)
        ((cechDegreeZeroRestriction X F V hV x) (τ ∘ k.succAbove))) = 0
  have hle (k : Fin 2) : CechCochains.inter V (τ ∘ k.succAbove) ≤ U := by
    simpa [CechCochains.inter] using hV ((τ ∘ k.succAbove) 0)
  have hterm (k : Fin 2) :
      CechCochains.restr F (CechCochains.inter_le_omit V τ k)
          ((cechDegreeZeroRestriction X F V hV x) (τ ∘ k.succAbove)) =
        CechCochains.restr F ((CechCochains.inter_le_omit V τ k).trans (hle k)) x.down :=
    CechCochains.restr_restr (ℱ := F) (hle k) (CechCochains.inter_le_omit V τ k) x.down
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul]
  rw [hterm 0, hterm 1, add_neg_cancel]

/-- The canonical augmentation from sections on `U` to alternating degree-zero Čech cochains. -/
noncomputable def alternatingCechAugmentation (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    AddCommGrpCat.of (ULift.{v} (F.obj (op U) : Type w)) ⟶
      (alternatingCechComplex V F).X 0 :=
  AddCommGrpCat.ofHom <| (cechDegreeZeroRestriction X F V hV).codRestrict
      (CechCochains.alternatingSubgroup V F 0)
      (cechDegreeZeroRestriction_isAlternating X F V hV)

/-- The augmentation composed with the first differential of the alternating Čech complex is
zero, so it is a map of complexes into the complex augmented in degree zero. -/
@[reassoc]
lemma alternatingCechAugmentation_d (X : TopCat.{u})
    (F : TopCat.Presheaf Ab.{w} X) {I : Type v} {U : Opens X}
    (V : I → Opens X) (hV : ∀ j, V j ≤ U) :
    alternatingCechAugmentation X F V hV ≫
      (alternatingCechComplex V F).d 0 1 = 0 := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ Subtype.ext ?_)
  exact cechDegreeZeroRestriction_d X F V hV x

end Stacks.Cech

end
