module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of a finite locally free module is unique where the site is nonempty

A sheaf of modules on a ringed site which is finite locally free of rank `r` (Stacks 0409) and
also of rank `r'` has `r = r'` as soon as the site has an object over which the structure ring
is nonzero and every covering of such an object has a member over which it is again nonzero.
Over such a member both free presentations restrict, and on sections they give an isomorphism
`R^r ≅ R^{r'}` of modules over a nonzero commutative ring, which has the invariant basis number
property.

## Main results

* `Stacks.SheafOfModules.rank_eq_of_isColimit_cofan`: two presentations of a sheaf of modules as
  a finite coproduct of copies of the structure sheaf have the same number of summands once the
  ring of sections over some object has the strong rank condition.
* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.eq_of_isColimit_cofan_over`: a free
  presentation over a suitable object determines the rank.
* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.rank_eq`: the uniqueness of the rank
  of a finite locally free module.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sections over `T` of a coproduct of `r` copies of the structure sheaf form the free
module `R(T)^r`. -/
noncomputable def sectionsLinearEquivOfIsColimitCofan (M : _root_.SheafOfModules.{w} R) {r : ℕ}
    (ι : ∀ _ : Fin r, _root_.SheafOfModules.unit R ⟶ M) (hc : IsColimit (Cofan.mk M ι))
    (T : Cᵒᵖ) :
    ((_root_.SheafOfModules.evaluation R T).obj M) ≃ₗ[R.obj.obj T] (Fin r → R.obj.obj T) :=
  let f : Fin r → _root_.SheafOfModules.{w} R := fun _ => _root_.SheafOfModules.unit R
  haveI : HasCoproduct f := HasColimit.mk ⟨_, hc⟩
  haveI : HasBiproduct f := HasBiproduct.of_hasCoproduct f
  haveI : (_root_.SheafOfModules.evaluation R T).Additive := ⟨fun {_ _ _ _} => rfl⟩
  let e : M ≅ ⨁ f := hc.coconePointUniqueUpToIso (biproduct.isColimit f)
  (((_root_.SheafOfModules.evaluation R T).mapIso e ≪≫
    (_root_.SheafOfModules.evaluation R T).mapBiproduct f ≪≫
    ModuleCat.biproductIsoPi _).toLinearEquiv)

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Two presentations of a sheaf of modules as a finite coproduct of copies of the structure
sheaf have the same number of summands, provided the ring of sections over some object has the
strong rank condition (for instance, is a nonzero commutative ring). -/
theorem rank_eq_of_isColimit_cofan (M : _root_.SheafOfModules.{w} R) {r r' : ℕ}
    (ι : ∀ _ : Fin r, _root_.SheafOfModules.unit R ⟶ M) (hc : IsColimit (Cofan.mk M ι))
    (ι' : ∀ _ : Fin r', _root_.SheafOfModules.unit R ⟶ M) (hc' : IsColimit (Cofan.mk M ι'))
    (T : Cᵒᵖ) [StrongRankCondition (R.obj.obj T)] : r = r' := by
  have e := (sectionsLinearEquivOfIsColimitCofan M ι hc T).symm.trans
    (sectionsLinearEquivOfIsColimitCofan M ι' hc' T)
  simpa using e.finrank_eq

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A free presentation over an object fixes the rank.** Let `P` be a class of objects of a
ringed site over which the structure ring is nonzero, such that every covering sieve of a
member of `P` contains an arrow out of a member of `P`. If a sheaf of modules is finite locally
free of rank `r'` (Stacks 0409) and its restriction to a member `U` of `P` is a coproduct of `r`
copies of the structure sheaf, then `r = r'`. -/
theorem IsFiniteLocallyFreeOfRank.eq_of_isColimit_cofan_over
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {r r' : ℕ}
    (h' : IsFiniteLocallyFreeOfRank X F r') (P : X.C → Prop)
    (hP : ∀ U, P U → ∀ S ∈ X.J U, ∃ (W : X.C) (g : W ⟶ U), S g ∧ P W)
    (hnt : ∀ U, P U → Nontrivial (X.O.obj.obj (op U))) {U : X.C} (hU : P U)
    (hfree : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ F.over U,
      Nonempty (IsColimit (Cofan.mk (F.over U) ι))) : r = r' := by
  obtain ⟨I', V', f', hf', hfree'⟩ := h' U
  obtain ⟨W', g', hg', hW'⟩ := hP U hU _ hf'
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff V' f' g').1 hg'
  obtain ⟨ι₁, ⟨hc₁⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofanOfRank_over_of_le _ F
    (a ≫ f' j) hfree
  obtain ⟨ι₂, ⟨hc₂⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofanOfRank_over_of_le _ F a
    (hfree' j)
  have : Nontrivial ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W')) :=
    hnt W' hW'
  have : StrongRankCondition
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W').obj.obj (op (Over.mk (𝟙 W')))) :=
    commRing_strongRankCondition ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W'))
  exact Stacks.SheafOfModules.rank_eq_of_isColimit_cofan (F.over W') ι₁ hc₁ ι₂ hc₂
    (op (Over.mk (𝟙 W')))

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The rank of a finite locally free module is unique.** Let `P` be a class of objects of a
ringed site over which the structure ring is nonzero, such that every covering sieve of a
member of `P` contains an arrow out of a member of `P` (for the small étale site of a scheme:
the nonempty étale schemes). If a sheaf of modules is finite locally free both of rank `r` and
of rank `r'` (Stacks 0409) and `P` has a member, then `r = r'`. -/
@[sga "6 I 6.10" "more general"]
theorem IsFiniteLocallyFreeOfRank.rank_eq
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {r r' : ℕ}
    (h : IsFiniteLocallyFreeOfRank X F r) (h' : IsFiniteLocallyFreeOfRank X F r')
    (P : X.C → Prop) (hP : ∀ U, P U → ∀ S ∈ X.J U, ∃ (W : X.C) (g : W ⟶ U), S g ∧ P W)
    (hnt : ∀ U, P U → Nontrivial (X.O.obj.obj (op U))) {U : X.C} (hU : P U) : r = r' := by
  obtain ⟨I, V, f, hf, hfree⟩ := h U
  obtain ⟨W, g, hg, hW⟩ := hP U hU _ hf
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).1 hg
  exact h'.eq_of_isColimit_cofan_over P hP hnt hW
    (Stacks.SheafOfModules.exists_isColimitCofanOfRank_over_of_le _ F k (hfree i))

end AlgebraicGeometry.RingedSite
