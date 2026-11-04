module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The diagonal of a transformation representable by algebraic spaces

A morphism of presheaves on the big fppf site over a scheme which is representable by
algebraic spaces has a relative diagonal that is again representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diagonal`: the relative
  diagonal of a transformation representable by algebraic spaces is representable by
  algebraic spaces.

## Implementation notes

The relative diagonal is the canonical morphism from the source of the transformation to
the pullback of the transformation along itself, and representability by algebraic spaces is
tested after every base change from a scheme over the base.  Fixing a scheme-valued point
of that pullback amounts to fixing two points of the source agreeing over the target, and
the base change of the diagonal along it is identified with the base change of the diagonal
of the algebraic space `V` obtained by pulling the transformation back along their common
image.  The latter is representable because the diagonal of `V` is, so the base change is a
representable presheaf, hence an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_yoneda` and
`AlgebraicGeometry.isAlgebraicSpace_of_iso`.

Binary products of the big fppf category over `S` are obtained from its terminal object and
its fibre products, so they need not be assumed separately.

## References

* [Stacks Project, Tag 05LA](https://stacks.math.columbia.edu/tag/05LA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A representable presheaf on the big fppf site over `S` is an algebraic space. -/
private theorem isAlgebraicSpace_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [P.IsRepresentable] :
    IsAlgebraicSpace B S hS P :=
  isAlgebraicSpace_of_iso B S hS (Functor.reprW P)
    (isAlgebraicSpace_yoneda B S hS P.reprX)

/-- **Stacks Project, Tag 05LA.** The relative diagonal of a transformation representable
by algebraic spaces is representable by algebraic spaces. -/
@[stacks 05LA]
theorem isRepresentableByAlgebraicSpaces_diagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : IsRepresentableByAlgebraicSpaces B S hS a) :
    IsRepresentableByAlgebraicSpaces B S hS (pullback.diagonal a) := by
  classical
  let C := BigFppfOver B S hS
  have : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  show ∀ (U : C) (ξ : yoneda.obj U ⟶ pullback.diagonalObj a),
    IsAlgebraicSpace B S hS (pullback ξ (pullback.diagonal a))
  intro U ξ
  let η : yoneda.obj U ⟶ pullback a a := ξ
  let α : yoneda.obj U ⟶ F := η ≫ pullback.fst a a
  let β : yoneda.obj U ⟶ F := η ≫ pullback.snd a a
  let ξ' : yoneda.obj U ⟶ G := α ≫ a
  let V := pullback ξ' a
  let s (π : pullback a a ⟶ F) (h : π ≫ a = pullback.fst a a ≫ a) : yoneda.obj U ⟶ V :=
    pullback.lift (𝟙 _) (η ≫ π) (by simp [ξ', α, h])
  have hsfst (π h) : s π h ≫ pullback.fst ξ' a = 𝟙 _ := pullback.lift_fst _ _ _
  have hssnd (π h) : s π h ≫ pullback.snd ξ' a = η ≫ π := pullback.lift_snd _ _ _
  let s₁ := s (pullback.fst a a) rfl
  let s₂ := s (pullback.snd a a) pullback.condition.symm
  have hV : IsAlgebraicSpace B S hS V := ha U ξ'
  let dV := diag V
  let p : yoneda.obj U ⟶ V ⨯ V := prod.lift s₁ s₂
  let Q := pullback p dV
  have hQ : Q.IsRepresentable := by
    simpa [Q] using
      (yoneda_relativelyRepresentable_iff_pullback_representable dV).mp
        hV.diagonal_representable U (yonedaEquiv p)
  let P := pullback (pullback.diagonal a) η
  have hP (π : pullback a a ⟶ F) (hπ : pullback.diagonal a ≫ π = 𝟙 F) :
      pullback.fst (pullback.diagonal a) η = pullback.snd (pullback.diagonal a) η ≫ η ≫ π := by
    simpa [hπ] using pullback.condition (f := pullback.diagonal a) (g := η) =≫ π
  have hcompat : pullback.snd (pullback.diagonal a) η ≫ ξ' =
      pullback.fst (pullback.diagonal a) η ≫ a := by
    rw [hP _ (pullback.diagonal_fst a)]
    simp [ξ', α]
  let r : P ⟶ V := pullback.lift
    (pullback.snd (pullback.diagonal a) η)
    (pullback.fst (pullback.diagonal a) η) hcompat
  have hrfst : r ≫ pullback.fst ξ' a = pullback.snd (pullback.diagonal a) η :=
    pullback.lift_fst _ _ _
  have hrsnd : r ≫ pullback.snd ξ' a = pullback.fst (pullback.diagonal a) η :=
    pullback.lift_snd _ _ _
  have hr (π : pullback a a ⟶ F) (h : π ≫ a = pullback.fst a a ≫ a)
      (hπ : pullback.diagonal a ≫ π = 𝟙 F) :
      r = pullback.snd (pullback.diagonal a) η ≫ s π h := by
    apply pullback.hom_ext <;> simp [hsfst, hssnd, hrfst, hrsnd, hP π hπ]
  have hr₁ := hr _ rfl (pullback.diagonal_fst a)
  have hr₂ := hr _ pullback.condition.symm (pullback.diagonal_snd a)
  have hpull : pullback.snd (pullback.diagonal a) η ≫ p = r ≫ dV :=
    prod.hom_ext (by simpa [p, dV] using hr₁.symm) (by simpa [p, dV] using hr₂.symm)
  let m : P ⟶ Q := pullback.lift (pullback.snd (pullback.diagonal a) η) r hpull
  have hq₁ : pullback.fst p dV ≫ s₁ = pullback.snd p dV := by
    simpa [p, dV] using pullback.condition (f := p) (g := dV) =≫ prod.fst
  have hq₂ : pullback.fst p dV ≫ s₂ = pullback.snd p dV := by
    simpa [p, dV] using pullback.condition (f := p) (g := dV) =≫ prod.snd
  have hqcompat : (pullback.snd p dV ≫ pullback.snd ξ' a) ≫ pullback.diagonal a =
      pullback.fst p dV ≫ η := by
    apply pullback.hom_ext
    · simpa [α, s₁, hssnd] using (hq₁ =≫ pullback.snd ξ' a).symm
    · simpa [β, s₂, hssnd] using (hq₂ =≫ pullback.snd ξ' a).symm
  let n : Q ⟶ P := pullback.lift
    (pullback.snd p dV ≫ pullback.snd ξ' a) (pullback.fst p dV) hqcompat
  have hmfst : m ≫ pullback.fst p dV = pullback.snd (pullback.diagonal a) η :=
    pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd p dV = r := pullback.lift_snd _ _ _
  have hnfst : n ≫ pullback.fst (pullback.diagonal a) η =
      pullback.snd p dV ≫ pullback.snd ξ' a :=
    pullback.lift_fst _ _ _
  have hnsnd : n ≫ pullback.snd (pullback.diagonal a) η = pullback.fst p dV :=
    pullback.lift_snd _ _ _
  have hnr : n ≫ r = pullback.snd p dV := by
    rw [hr₁, ← Category.assoc, hnsnd, hq₁]
  have hmn : m ≫ n = 𝟙 P := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnfst, ← Category.assoc, hmsnd, hrsnd, Category.id_comp]
    · rw [Category.assoc, hnsnd, hmfst, Category.id_comp]
  have hnm : n ≫ m = 𝟙 Q := by
    apply pullback.hom_ext <;> simp [hmfst, hmsnd, hnsnd, hnr]
  let e : P ≅ Q := ⟨m, n, hmn, hnm⟩
  have : Q.IsRepresentable := hQ
  have : P.IsRepresentable := isRepresentable_of_natIso Q e.symm
  exact isAlgebraicSpace_of_iso B S hS (pullbackSymmetry (pullback.diagonal a) η)
    (isAlgebraicSpace_of_representable B S hS P)

end AlgebraicGeometry.Space

end
