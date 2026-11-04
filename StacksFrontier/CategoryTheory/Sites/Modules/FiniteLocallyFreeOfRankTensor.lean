module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The tensor product of modules of ranks `r` and `s` on a ringed site has rank `r s`

Let `X` be a ringed site and `F`, `G` finite locally free `𝒪_X`-modules of ranks `r` and `s` (the
rank clause of Stacks 0409). Then `F ⊗ G` is finite locally free of rank `r s`: on a common
refinement of coverings trivializing `F` and `G`, the tensor product of a free module on `r`
generators with one on `s` generators is free on the `r s` pairs. This refines Stacks 03L6 (2),
which records only finite local freeness.

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.isLocallyFreeOnSiteWith_tensor_of`: local freeness
  with local bases in classes `P` and `Q` gives, for the tensor product, local bases in any class
  containing the products `A × B` with `A ∈ P`, `B ∈ Q`.
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_sheafTensor`: **the tensor product of
  modules of ranks `r` and `s` has rank `r s`.**

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.TensorLocalProperties

/-- **Local bases of a tensor product.** If `F` is locally free with local bases in the class
`P` and `G` with local bases in the class `Q`, then `F ⊗ G` is locally free with local bases in
every class `T` containing the products `A × B` with `A ∈ P` and `B ∈ Q`. -/
theorem isLocallyFreeOnSiteWith_tensor_of (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P Q T : Type w → Prop} (hPQ : ∀ {A B : Type w}, P A → Q B → T (A × B))
    {F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hF : IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P F)
    (hG : IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Q G) :
    IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) := by
  intro U
  obtain ⟨IF, VF, fF, hFcov, hFfree⟩ := hF U
  obtain ⟨IG, VG, fG, hGcov, hGfree⟩ := hG U
  let SF : Sieve U := Sieve.ofArrows VF fF
  let SG : Sieve U := Sieve.ofArrows VG fG
  let K : Type (max u v) := {p : Σ V : X.C, V ⟶ U // SF p.2 ∧ SG p.2}
  let W : K → X.C := fun p => p.1.1
  let fW : ∀ p, W p ⟶ U := fun p => p.1.2
  have hle : SF ⊓ SG ≤ Sieve.ofArrows W fW := fun V g hg =>
    Sieve.ofArrows_mk W fW ⟨⟨V, g⟩, hg⟩
  refine ⟨K, W, fW, X.J.superset_covering hle (X.J.intersection_covering hFcov hGcov),
    fun p => ?_⟩
  obtain ⟨iF, gF, -⟩ := (Sieve.mem_ofArrows_iff VF fF (fW p)).1 p.2.1
  obtain ⟨iG, gG, -⟩ := (Sieve.mem_ofArrows_iff VG fG (fW p)).1 p.2.2
  obtain ⟨BF, hBF, ιF, ⟨hιF⟩⟩ := hFfree iF
  obtain ⟨BG, hBG, ιG, ⟨hιG⟩⟩ := hGfree iG
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  obtain ⟨κF, hκF⟩ := freeModel_over_isFree R BF (VF iF)
  obtain ⟨κG, hκG⟩ := freeModel_over_isFree R BG (VG iG)
  have restrict : ∀ {H : _root_.SheafOfModules.{w} R} {B : Type w} {V W : X.C} (g : W ⟶ V),
      (H.over V ≅ (freeModel R B).over V) → (H.over W ≅ (freeModel R B).over W) :=
    fun g e => ((_root_.SheafOfModules.overFunctorMap R g).app _).symm ≪≫
      (_root_.SheafOfModules.overMap R g).mapIso e ≪≫
      (_root_.SheafOfModules.overFunctorMap R g).app _
  let e := tensor_over_congr X.O (W p) (restrict gF (hιF.coconePointUniqueUpToIso hκF.some))
    (restrict gG (hιG.coconePointUniqueUpToIso hκG.some)) ≪≫
    (_root_.SheafOfModules.overFunctor R (W p)).mapIso (freeModel_tensorIso X.O BF BG)
  obtain ⟨κ, hκ⟩ := freeModel_over_isFree R (BF × BG) (W p)
  exact ⟨BF × BG, hPQ hBF hBG, fun b => κ b ≫ e.inv,
    ⟨hκ.some.ofIsoColimit (Cofan.ext e.symm fun b => rfl)⟩⟩

end Stacks.SheafOfModules.TensorLocalProperties

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.TensorLocalProperties

variable (X : RingedSite.{u, v, w})

/-- Rank `r` is local freeness with local bases of cardinality `r`. -/
theorem isFiniteLocallyFreeOfRank_iff_isLocallyFreeOnSiteWith
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ) :
    IsFiniteLocallyFreeOfRank X F r ↔
      IsLocallyFreeOnSiteWith (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (fun B => Finite B ∧ Nat.card B = r) F := by
  refine forall_congr' fun U => ?_
  constructor
  · rintro ⟨I, V, f, hcov, hfree⟩
    refine ⟨I, V, f, hcov, fun i => ?_⟩
    obtain ⟨ι, ⟨hι⟩⟩ := hfree i
    exact ⟨ULift.{w} (Fin r), ⟨inferInstance, by simp⟩, fun b => ι b.down,
      ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk (F.over (V i)) ι) hι⟩⟩
  · rintro ⟨I, V, f, hcov, hfree⟩
    refine ⟨I, V, f, hcov, fun i => ?_⟩
    obtain ⟨B, ⟨hB, rfl⟩, ι, ⟨hι⟩⟩ := hfree i
    exact ⟨fun j => ι ((Finite.equivFin B).symm j),
      ⟨Cofan.isColimitEquivOfEquiv (Finite.equivFin B).symm (Cofan.mk (F.over (V i)) ι) hι⟩⟩

/-- **The tensor product of finite locally free modules of ranks `r` and `s` on a ringed site has
rank `r s`.** -/
theorem isFiniteLocallyFreeOfRank_sheafTensor
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {r s : ℕ}
    (hF : IsFiniteLocallyFreeOfRank X F r) (hG : IsFiniteLocallyFreeOfRank X G s) :
    IsFiniteLocallyFreeOfRank X
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) (r * s) := by
  rw [isFiniteLocallyFreeOfRank_iff_isLocallyFreeOnSiteWith] at hF hG ⊢
  refine isLocallyFreeOnSiteWith_tensor_of X ?_ hF hG
  rintro A B ⟨hA, rfl⟩ ⟨hB, rfl⟩
  exact ⟨inferInstance, Nat.card_prod A B⟩

end AlgebraicGeometry.RingedSite

end
