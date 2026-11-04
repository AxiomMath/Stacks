module

public import StacksFrontier.RingTheory.ChartedFunctor.CechTangent

/-!
# Lifting along a square-zero thickening of the base, for a charted sheaf

Let `F` be a functor on bounded `R`-algebras with an étale chart `Hom_R(C, -) ⟶ F`, let `I` be an
ideal of `R` of square zero, and let `x` be a section of `F` over `R ⧸ I`. Suppose given a
faithfully flat `R`-algebra `S` and an algebra map `ρ : C → S` whose reduction is a chart point
over `S ⧸ I S` of the pull-back of `x` — so the pull-back of `x` lifts to `S`, through the chart —
and suppose `F` satisfies descent along `R → S` and is separated along `R ⧸ I → S ⧸ I S`. Then
`x` lifts to `R`.

This is the trivialisation of the torsor of lifts, step (II) of [Stacks Project, Tag 04AM], in
algebraic form. The lift `z` over `S` gives the difference `θ` of its two pull-backs to
`S ⊗_R S`, a `1`-cocycle of the Čech complex of the tangent by the torsor identities and their
compatibility with maps (`Stacks.ChartedFunctor.Lifts.diff_add_diff`,
`Stacks.ChartedFunctor.Lifts.map_diff`). The Čech complex is exact in degree one
(`Stacks.ChartedFunctor.Cech.exact`), so `θ = d η`; correcting `z` by `-η` makes the two
pull-backs agree, and descent along `R → S` produces the lift over `R`.

## Main results

* `Stacks.ChartedFunctor.exists_lift_of_faithfullyFlat`: the statement above.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace Stacks.ChartedFunctor

open BaseSection Cech

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
  {F : BoundedAlg R κ ⥤ Type u} {hR : #R < κ} {I : Ideal R} {x : F.obj (quot (base hR) I)}

/-- The image of a lift of the pulled-back section under an algebra map. -/
abbrev Lmap {P Q : BoundedAlg R κ} (f : P ⟶ Q) :
    Lifts F P (ideal I P) (pt hR I x P) → Lifts F Q (ideal I Q) (pt hR I x Q) :=
  Lifts.map f (ideal_le_comap I f) (pt_map f)

/-- The image of a lift under a composite of algebra maps is the iterated image. -/
lemma Lmap_comp {P Q W : BoundedAlg R κ} (f : P ⟶ Q) (g : Q ⟶ W)
    (z : Lifts F P (ideal I P) (pt hR I x P)) : Lmap g (Lmap f z) = Lmap (f ≫ g) z :=
  Lifts.map_map _ _ _ _ _ _ z

omit [Fact (ℵ₀ < κ)] in
/-- Equal algebra maps have the same image on lifts. -/
lemma Lmap_eq {P Q : BoundedAlg R κ} {f g : P ⟶ Q} (h : f = g)
    (z : Lifts F P (ideal I P) (pt hR I x P)) : Lmap f z = Lmap g z := by
  subst h; rfl

/-- The difference of two lifts, as an element of `T`. -/
def diffT {P : BoundedAlg R κ} (z z' : Lifts F P (ideal I P) (pt hR I x P)) : T hR I x P :=
  Lifts.diff z z'

section ChartPoint

variable (hI : I ^ 2 = ⊥) {P : BoundedAlg R κ} [hP : Fact (HasChartPoint F (pt hR I x P))]
include hI

/-- The differences of lifts add up: `diffT z₁ z₂ + diffT z₂ z₃ = diffT z₁ z₃`. -/
lemma diffT_add_diffT (z₁ z₂ z₃ : Lifts F P (ideal I P) (pt hR I x P)) :
    diffT z₁ z₂ + diffT z₂ z₃ = diffT z₁ z₃ :=
  Lifts.diff_add_diff (ideal_sq I hI P) hP.out.choose hP.out.choose_spec.choose_spec z₁ z₂ z₃

/-- The difference of a lift with itself is zero. -/
lemma diffT_self (z : Lifts F P (ideal I P) (pt hR I x P)) : diffT z z = 0 :=
  Lifts.diff_self (ideal_sq I hI P) hP.out.choose hP.out.choose_spec.choose_spec z

/-- Swapping two lifts negates their difference. -/
lemma diffT_swap (z z' : Lifts F P (ideal I P) (pt hR I x P)) :
    diffT z' z = -diffT z z' := by
  have h := diffT_add_diffT hI z z' z
  rw [diffT_self hI] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Two lifts with zero difference are equal. -/
lemma eq_of_diffT_eq_zero (z z' : Lifts F P (ideal I P) (pt hR I x P)) (h : diffT z z' = 0) :
    z = z' :=
  Lifts.eq_of_diff_eq_zero (ideal_sq I hI P) hP.out.choose hP.out.choose_spec.choose_spec z z' h

/-- Every element of `T` is the difference of a given lift and some other lift. -/
lemma exists_diffT_eq (z : Lifts F P (ideal I P) (pt hR I x P)) (w : T hR I x P) :
    ∃ z', diffT z z' = w :=
  Lifts.exists_diff_eq (ideal_sq I hI P) hP.out.choose hP.out.choose_spec.choose_spec z w

/-- The difference of lifts commutes with the maps of the Čech nerve, at chart points. -/
lemma dT_diffT {Q : BoundedAlg R κ} (f : P ⟶ Q) [Fact (HasChartPoint F (pt hR I x Q))]
    (z z' : Lifts F P (ideal I P) (pt hR I x P)) :
    dT f (diffT z z') = diffT (Lmap f z) (Lmap f z') :=
  Lifts.map_diff f (ideal_le_comap I f) (pt_map f) (ideal_sq I hI P) (ideal_sq I hI Q)
    hP.out.choose hP.out.choose_spec.choose_spec z z'

end ChartPoint

/-- **Lifting along a square-zero thickening of the base.** -/
theorem exists_lift_of_faithfullyFlat (c : EtaleChart F) (hI : I ^ 2 = ⊥) (S : BoundedAlg R κ)
    [Module.FaithfullyFlat R S.obj]
    (hdesc : ∀ z : F.obj S, F.map (δ00 S) z = F.map (δ01 S) z →
      ∃ z₀ : F.obj (base hR), F.map (toP hR S) z₀ = z)
    (hsep : Function.Injective (F.map (quotMap (toP hR S) (le_comap_ideal hR I S))))
    (ρ : c.C ⟶ S.obj)
    (hρ : c.α.app (quot S (ideal I S)) (ρ ≫ (quotMk S (ideal I S)).hom) = pt hR I x S) :
    ∃ z₀ : F.obj (base hR), F.map (quotMk (base hR) I) z₀ = x := by
  have : Fact (HasChartPoint F (pt hR I x S)) := ⟨⟨c, _, hρ⟩⟩
  let z : Lifts F S (ideal I S) (pt hR I x S) := ⟨c.α.app S ρ, by rw [c.map_α, hρ]⟩
  -- the difference of the two pull-backs is a cocycle
  let θ : T hR I x (L1 S) := diffT (Lmap (δ01 S) z) (Lmap (δ00 S) z)
  have hθ : d1 S θ = 0 := by
    simp only [θ, LinearMap.add_apply, LinearMap.sub_apply]
    rw [dT_diffT hI, dT_diffT hI, dT_diffT hI, Lmap_comp, Lmap_comp, Lmap_comp, Lmap_comp,
      Lmap_comp, Lmap_comp, Lmap_eq (δ10_δ01 S), Lmap_eq (δ10_δ00 S), Lmap_eq (δ11_δ01 S),
      sub_add_eq_add_sub, add_comm, diffT_add_diffT hI, sub_self]
  -- the cocycle is a coboundary
  obtain ⟨η, hη⟩ := (exact (F := F) (hR := hR) (I := I) (x := x) S hI θ).1 hθ
  -- correct the lift by `-η`
  obtain ⟨z', hz'⟩ := exists_diffT_eq hI z (-η)
  have hagree : Lmap (δ01 S) z' = Lmap (δ00 S) z' := by
    refine eq_of_diffT_eq_zero hI _ _ ?_
    have e₁ := diffT_add_diffT hI (Lmap (δ01 S) z') (Lmap (δ01 S) z) (Lmap (δ00 S) z')
    have e₂ := diffT_add_diffT hI (Lmap (δ01 S) z) (Lmap (δ00 S) z) (Lmap (δ00 S) z')
    rw [← e₁, ← e₂, diffT_swap hI (Lmap (δ01 S) z), ← dT_diffT hI, ← dT_diffT hI, hz']
    have hθη : dT (δ00 S) η - dT (δ01 S) η = diffT (Lmap (δ01 S) z) (Lmap (δ00 S) z) := hη
    rw [map_neg, map_neg, ← hθη]
    abel
  obtain ⟨z₀, hz₀⟩ := hdesc z'.1 (congrArg Subtype.val hagree).symm
  refine ⟨z₀, hsep ?_⟩
  rw [← Functor.map_comp_apply, quotMk_quotMap, Functor.map_comp_apply, hz₀]
  exact z'.2
end Stacks.ChartedFunctor

end
