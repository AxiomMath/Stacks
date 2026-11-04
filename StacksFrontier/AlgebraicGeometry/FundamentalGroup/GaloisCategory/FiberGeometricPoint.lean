module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer

/-!
# A point of the geometric fibre of a finite étale cover is a geometric point of the cover

Let `S` be a scheme, `s` a geometric point of it and `T → S` a finite étale cover. A point of the
geometric fibre of `T` at `s`, in the sense of `AlgebraicGeometry.finiteEtaleFiberFunctor`, is a
morphism `Spec κ(s) ⟶ T` over `s`; reading it as the structure morphism of a geometric point of
`T` with the same residue field turns it into a geometric point `t` of `T` lying over `s`. This
file makes that reading, and records the two facts about it that the dictionary of Stacks 0DV5
over the cover needs: that `t` lies over `s` on the nose, and that the point of the fibre `t`
determines by `AlgebraicGeometry.finiteEtaleOverSourcePoint` is the given one.

The second fact can only be stated as a `HEq`: the two points live in the geometric fibres at
`t.map T.hom` and at `s`, which are subtypes of the same morphism type cut out by two
propositionally — not syntactically — equal conditions. Both are packaged into one existential
statement, which is the form in which a consumer can substitute `s` away and recover an equality.

## Main definitions

* `AlgebraicGeometry.finiteEtaleFiberGeometricPoint`: the geometric point of the cover attached to
  a point of the geometric fibre.

## Main results

* `AlgebraicGeometry.map_finiteEtaleFiberGeometricPoint`: it lies over the given geometric point.
* `AlgebraicGeometry.exists_geometricPoint_heq_finiteEtaleOverSourcePoint`: the two facts above,
  packaged.
* `AlgebraicGeometry.smul_finiteEtaleOverSourcePoint_eq`: **the monodromy of a finite étale cover
  stabilises the chosen point of its geometric fibre.** This is the easy inclusion of
  `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`, in the form the dictionary
  consumes: the action of `π₁(T, t)` on the stalk is the restriction of the action of `π₁(S, s)`
  along a homomorphism landing in the stabiliser.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **A point of the geometric fibre of a finite étale cover, read as a geometric point of the
cover.** Its residue field is that of the base point and its structure morphism is the point of
the fibre. -/
def finiteEtaleFiberGeometricPoint (s : GeometricPoint S) (T : FiniteEtaleOver S)
    (y : (finiteEtaleFiberFunctor s).obj T) : GeometricPoint T.left :=
  @GeometricPoint.mk T.left s.residueField s.field_residueField s.isAlgClosed_residueField y.1

/-- The geometric point of the cover attached to a point of the geometric fibre lies over the
base point. -/
theorem map_finiteEtaleFiberGeometricPoint (s : GeometricPoint S) (T : FiniteEtaleOver S)
    (y : (finiteEtaleFiberFunctor s).obj T) :
    (finiteEtaleFiberGeometricPoint s T y).map T.hom = s := by
  change @GeometricPoint.mk S s.residueField s.field_residueField
    s.isAlgClosed_residueField (y.1 ≫ T.hom) = s
  rw [y.2]

/-- **A point of the geometric fibre of a finite étale cover comes from a geometric point of the
cover.** There is a geometric point `t` of `T` lying over `s` whose associated point of the
geometric fibre of `T → S` is the given one. -/
theorem exists_geometricPoint_heq_finiteEtaleOverSourcePoint (s : GeometricPoint S)
    (T : FiniteEtaleOver S) (y : (finiteEtaleFiberFunctor s).obj T) :
    ∃ (t : GeometricPoint T.left) (_ : t.map T.hom = s),
      HEq (finiteEtaleOverSourcePoint (f := T.hom) T.prop t) y := by
  refine ⟨finiteEtaleFiberGeometricPoint s T y,
    map_finiteEtaleFiberGeometricPoint s T y, ?_⟩
  refine (Subtype.heq_iff_coe_eq fun _ ↦ ?_).2 rfl
  exact ⟨fun h ↦ h.trans y.2, fun h ↦ h.trans y.2.symm⟩

/-- **The monodromy of a finite étale cover stabilises the chosen point of its geometric fibre.**
This is the inclusion of the image of `π₁(T, t) → π₁(S, t ∘ f)` in the stabiliser, which is one
half of `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`. -/
theorem smul_finiteEtaleOverSourcePoint_eq {T : Scheme.{u}} {f : T ⟶ S} [ConnectedSpace S]
    [ConnectedSpace T] (hf : finiteEtale f) (t : GeometricPoint T)
    (σ : EtaleFundamentalGroup T t) :
    etaleFundamentalGroupMap f t σ • finiteEtaleOverSourcePoint hf t =
      finiteEtaleOverSourcePoint hf t :=
  show etaleFundamentalGroupMap f t σ ∈
      MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
        (finiteEtaleOverSourcePoint hf t) from
    (range_etaleFundamentalGroupMap_eq_stabilizer hf t) ▸ ⟨σ, rfl⟩

end AlgebraicGeometry

end
