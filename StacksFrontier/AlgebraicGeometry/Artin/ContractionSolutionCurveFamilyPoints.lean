module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizer
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving

/-!
# Solutions of the contraction problem when `W` has at most one point

Let `s` be a solution of Artin's contraction problem of Stacks 0GH8 with target `X`, so that
`s.a : X_{/T} ≅ W`. When the formal algebraic space `W` has at most one point, in the sense
that any two of its sections over spectra of fields restrict to a common section over the
spectrum of a common field extension, the closed subset `T ⊆ |X|` has at most one point. If
moreover `T'` is nonempty and `U` has point set `|X| ∖ T`, the contraction `f : X' ⟶ X` is
surjective on points and `T` is the single point `f(T')`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAtMostOnePoint`: an fppf sheaf of `Type (u + 1)` on the
  big fppf site of `S` has at most one point.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.subsingleton_T`: if `W` has at most
  one point, then so does `T`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.surjective_pointsMap_f`: if moreover
  `T'` is nonempty and `|U| = |X| ∖ T`, then `|f| : |X'| ⟶ |X|` is surjective.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.exists_T_eq_singleton`: if `W` has at
  most one point and `T'` is nonempty, then `T` is a single point, the image of `T'`.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An fppf sheaf `W` of `Type (u + 1)` on the big fppf site of `S` *has at most one point*
when any two of its sections over spectra of fields have a common field extension: for
sections `w₁` over `Spec K₁` and `w₂` over `Spec K₂`, there are a field `L` and morphisms
`Spec L ⟶ Spec K₁`, `Spec L ⟶ Spec K₂` over `S` along which `w₁` and `w₂` restrict to the same
section over `Spec L`. -/
def HasAtMostOnePoint (W : FppfSheaf B S hS) : Prop :=
  ∀ (K₁ K₂ : Type u) [Field K₁] [Field K₂] (h₁ : B.Contains (Spec (.of K₁)))
    (h₂ : B.Contains (Spec (.of K₂))) (p₁ : Spec (.of K₁) ⟶ S) (p₂ : Spec (.of K₂) ⟶ S)
    (w₁ : W.obj.obj (op (Over.mk (⟨p₁⟩ : B.obj h₁ ⟶ B.obj hS))))
    (w₂ : W.obj.obj (op (Over.mk (⟨p₂⟩ : B.obj h₂ ⟶ B.obj hS)))),
    ∃ (L : Type u) (_ : Field L) (hL : B.Contains (Spec (.of L))) (pL : Spec (.of L) ⟶ S)
      (q₁ : Over.mk (⟨pL⟩ : B.obj hL ⟶ B.obj hS) ⟶ Over.mk (⟨p₁⟩ : B.obj h₁ ⟶ B.obj hS))
      (q₂ : Over.mk (⟨pL⟩ : B.obj hL ⟶ B.obj hS) ⟶ Over.mk (⟨p₂⟩ : B.obj h₂ ⟶ B.obj hS)),
      W.obj.map q₁.op w₁ = W.obj.map q₂.op w₂

end FormalSpace

namespace Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X)

/-- If `W` has at most one point, then the closed subset `T ⊆ |X|` of a solution has at most
one point: the field-valued representatives of two points of `T` are sections of the
completion `X_{/T}`, whose images in `W` have a common field extension, and the isomorphism
`a : X_{/T} ≅ W` carries it back to a common extension of the two representatives. -/
theorem subsingleton_T (hW : FormalSpace.HasAtMostOnePoint c.W) : s.T.Subsingleton := by
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨p₁, rfl⟩ := Quot.exists_rep t₁
  obtain ⟨p₂, rfl⟩ := Quot.exists_rep t₂
  let e := Space.completionSheafIsoSubfunctor B S hS s.isAlgebraicSpace_X.isSheaf s.T
  let σ : ∀ p : Space.FieldValuedPoint B S hS X, Quot.mk _ p ∈ s.T →
      (Space.completionSheaf B S hS X s.T).obj.obj (op p.siteObject) := fun p hp =>
    e.inv.app _ ⟨ULift.up p.value, (Space.hasImageIn_iff_class_mem B S hS X s.T p).2 hp⟩
  obtain ⟨L, _, hL, pL, q₁, q₂, hq⟩ := hW p₁.carrier p₂.carrier p₁.contained p₂.contained
    p₁.toBase p₂.toBase (s.a.hom.hom.app _ (σ p₁ ht₁)) (s.a.hom.hom.app _ (σ p₂ ht₂))
  have hinv : ∀ (U : (BigFppfOver B S hS)ᵒᵖ)
      (x : (Space.completionSheaf B S hS X s.T).obj.obj U),
      s.a.inv.hom.app U (s.a.hom.hom.app U x) = x := fun U x => by
    change (s.a.hom ≫ s.a.inv).hom.app U x = x
    rw [s.a.hom_inv_id]
    rfl
  have hσ : (Space.completionSheaf B S hS X s.T).obj.map q₁.op (σ p₁ ht₁) =
      (Space.completionSheaf B S hS X s.T).obj.map q₂.op (σ p₂ ht₂) := by
    rw [← hinv _ ((Space.completionSheaf B S hS X s.T).obj.map q₁.op (σ p₁ ht₁)),
      ← hinv _ ((Space.completionSheaf B S hS X s.T).obj.map q₂.op (σ p₂ ht₂)),
      NatTrans.naturality_apply s.a.hom.hom q₁.op, NatTrans.naturality_apply s.a.hom.hom q₂.op,
      hq]
  have key : ∀ (p : Space.FieldValuedPoint B S hS X) (hp : Quot.mk _ p ∈ s.T)
      (q : Over.mk (⟨pL⟩ : B.obj hL ⟶ B.obj hS) ⟶ p.siteObject),
      (e.hom.app _ ((Space.completionSheaf B S hS X s.T).obj.map q.op (σ p hp))).1.down =
        X.map q.op p.value := by
    intro p hp q
    rw [NatTrans.naturality_apply e.hom q.op]
    have he : e.hom.app _ (σ p hp) =
        ⟨ULift.up p.value, (Space.hasImageIn_iff_class_mem B S hS X s.T p).2 hp⟩ := by
      change (e.inv ≫ e.hom).app _ _ = _
      rw [e.inv_hom_id]
      rfl
    rw [he]
    rfl
  have h₁ := key p₁ ht₁ q₁
  have h₂ := key p₂ ht₂ q₂
  rw [hσ] at h₁
  refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X
    ⟨⟨L, hL, pL, X.map q₁.op p₁.value⟩, ⟨q₁, rfl⟩, ⟨q₂, ?_⟩⟩
  exact h₂.symm.trans h₁

/-- If `W` has at most one point and `T'` is nonempty, then `T` is a single point, the image of
`T'` under `|f| : |X'| ⟶ |X|`: the image of `T'` lies in `T` by condition (1), and `T` has at
most one point. -/
theorem exists_T_eq_singleton (hW : FormalSpace.HasAtMostOnePoint c.W) (hT' : c.T'.Nonempty) :
    ∃ x, s.T = {x} ∧ Space.pointsMap B S hS c.X' s.f '' c.T' = {x} := by
  obtain ⟨y, hy⟩ := hT'
  have himage : Space.pointsMap B S hS c.X' s.f '' c.T' ⊆ s.T := by
    rw [← s.preimage_T]
    exact Set.image_preimage_subset _ _
  have hx : Space.pointsMap B S hS c.X' s.f y ∈ s.T := himage ⟨y, hy, rfl⟩
  have hT : s.T = {Space.pointsMap B S hS c.X' s.f y} :=
    (s.subsingleton_T hW).eq_singleton_of_mem hx
  refine ⟨_, hT, ?_⟩
  rw [← hT]
  exact himage.antisymm (hT ▸ Set.singleton_subset_iff.2 ⟨y, hy, rfl⟩)

/-- If `W` has at most one point, `T'` is nonempty and the open subspace `U` has point set
`|X| ∖ T`, then `|f| : |X'| ⟶ |X|` is surjective: the single point of `T` is the image of a
point of `T'`, and the points of `|X| ∖ T = |U|` are images of points of `U'`, which `f` maps
onto `U`. -/
theorem surjective_pointsMap_f (hW : FormalSpace.HasAtMostOnePoint c.W) (hT' : c.T'.Nonempty)
    (hU : Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) :
    Function.Surjective (Space.pointsMap B S hS c.X' s.f) := by
  intro x
  by_cases hx : x ∈ s.T
  · obtain ⟨z, hT, himage⟩ := s.exists_T_eq_singleton hW hT'
    rw [hT, Set.mem_singleton_iff] at hx
    obtain ⟨y, -, hy⟩ : x ∈ Space.pointsMap B S hS c.X' s.f '' c.T' := by
      rw [himage, hx]; rfl
    exact ⟨y, hy⟩
  · rw [← Set.mem_compl_iff, ← hU, ← s.range_pointsMap_U'_comp_f, Space.pointsMap_comp] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨_, hy⟩

end Artin.ContractionSituation.Solution

end AlgebraicGeometry

end
