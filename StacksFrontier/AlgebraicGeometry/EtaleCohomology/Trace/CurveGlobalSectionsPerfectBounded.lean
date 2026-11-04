module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Perfectness of a right derived functor on bounded complexes

Let `F : 𝒜 ⥤ Mod_R` be an additive functor from an abelian category with enough injectives. If
`RF(G[0])` is perfect for every object `G` of a class closed under isomorphism, then `RF(C)` is
perfect for every bounded complex `C` whose terms lie in the class: the stupid truncations present
`C` as an iterated extension of its terms placed in their degrees, `RF` is triangulated and
commutes with shifts, and perfect complexes are closed under shifts and under extensions (Tag
066R). This is the reduction to a single sheaf in the proof of [Stacks, Tag 03TV].

## Main results

* `StacksDraft.Perfect.IsPerfect.shift`: perfectness is invariant under shifts.
* `StacksDraft.Perfect.isPerfect_rightDerivedFunctorPlus_of_bounded`: the reduction.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated HomologicalComplex ComplexShape

universe w v u

namespace StacksDraft.Perfect

/-- Perfectness is invariant under shifts. -/
theorem IsPerfect.shift {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {X : DerivedCategory (ModuleCat.{v} R)} (h : IsPerfect X) (n : ℤ) : IsPerfect (X⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := h
  refine ⟨P⟦n⟧, a - n, b - n, P.isStrictlyGE_shift a n (a - n) (by omega),
    P.isStrictlyLE_shift b n (b - n) (by omega), fun i => hf _, fun i => hp _, ?_⟩
  exact ⟨(shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n).mapIso e ≪≫
    (DerivedCategory.Q.commShiftIso n).symm.app P⟩

attribute [local instance] HasDerivedCategory.standard
  Functor.commShiftRightDerivedFunctorPlus Functor.isTriangulated_rightDerivedFunctorPlus

variable {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A] {R : Type u} [Ring R]
  (F : A ⥤ ModuleCat.{v} R) [F.Additive] (good : A → Prop)
  (hiso : ∀ {X X' : A}, (X ≅ X') → good X → good X')
  (hgood : ∀ G, good G → IsPerfect (DerivedCategory.Plus.ι.obj
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj G))))

include hgood in
/-- `RF(G[i])` is perfect for `G` in the class, in every degree `i`. -/
lemma isPerfect_rightDerivedFunctorPlus_singleFunctor (G : A) (hG : good G) (i : ℤ) :
    IsPerfect (DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A i).obj G))) := by
  let e₁ : (DerivedCategory.Plus.singleFunctor A i).obj G ≅
      ((DerivedCategory.Plus.singleFunctor A 0).obj G)⟦-i⟧ :=
    (((DerivedCategory.Plus.singleFunctors A).shiftIso (-i) i 0 (by omega)).app G).symm
  refine isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso e₁ ≪≫
      (F.rightDerivedFunctorPlus.commShiftIso (-i)).app _) ≪≫
      (DerivedCategory.Plus.ι.commShiftIso (-i)).app _) ((hgood G hG).shift (-i))

include hgood in
/-- `RF(C)` is perfect for a complex `C` concentrated in one degree with term in the class. -/
lemma isPerfect_rightDerivedFunctorPlus_of_single (C : CochainComplex A ℤ)
    (hC : CochainComplex.plus A C) (a : ℤ) (hz : ∀ i, i ≠ a → IsZero (C.X i)) (ha : good (C.X a)) :
    IsPerfect (DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (Functor.plusObj C hC)))) :=
  isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Qh.mapIso (Functor.isoSingleFunctorObjPlus C hC a hz) ≪≫
        ((Functor.singleFunctorPlusIsoCompQh a).app (C.X a)).symm)))
    (isPerfect_rightDerivedFunctorPlus_singleFunctor F good hgood (C.X a) ha a)

include hiso hgood in
/-- `RF(C)` is perfect for a complex `C` concentrated in degrees `a, …, a + m` whose terms lie in
the class. -/
lemma isPerfect_rightDerivedFunctorPlus_of_bounded_aux (m : ℕ) :
    ∀ (C : CochainComplex A ℤ) (a : ℤ) (hC : CochainComplex.plus A C),
      (∀ i, i < a ∨ a + m < i → IsZero (C.X i)) → (∀ i, a ≤ i → i ≤ a + m → good (C.X i)) →
      IsPerfect (DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (Functor.plusObj C hC)))) := by
  induction m with
  | zero =>
    intro C a hC hz hg
    exact isPerfect_rightDerivedFunctorPlus_of_single F good hgood C hC a
      (fun i hi => hz i (by omega)) (hg a le_rfl (by simp))
  | succ m ih =>
    intro C a hC hz hg
    let T := (DerivedCategory.Plus.ι.mapTriangle.obj (F.rightDerivedFunctorPlus.mapTriangle.obj
      (DerivedCategory.Plus.Qh.mapTriangle.obj (Functor.stupidTruncTrianglehPlus C a hC))))
    have hT : T ∈ distTriang _ := DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _
        (DerivedCategory.Plus.Qh.map_distinguished _
          (Functor.stupidTruncTrianglehPlus_distinguished C a hC)))
    have h₁ : IsPerfect T.obj₁ := ih _ (a + 1) _ (fun i hi => by
        rcases hi with hi | hi
        · exact Functor.isZero_stupidTruncGE_X_of_lt C (a + 1) i hi
        · exact Functor.isZero_stupidTrunc_X_of_isZero C _ i (hz i (by omega)))
      (fun i hi hi' => hiso (C.stupidTruncXIso (embeddingUpIntGE (a + 1))
        (i := (i - (a + 1)).toNat) (by rw [Functor.embeddingUpIntGE_f']; omega)).symm
        (hg i (by omega) (by omega)))
    have h₃ : IsPerfect T.obj₃ := isPerfect_rightDerivedFunctorPlus_of_single F good hgood _ _ a
      (fun i hi => by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact Functor.isZero_stupidTrunc_X_of_isZero C _ i (hz i (by omega))
        · exact Functor.isZero_stupidTruncLE_X_of_lt C a i hi)
      (hiso (C.stupidTruncXIso (embeddingUpIntLE a) (i := 0)
        (by rw [Functor.embeddingUpIntLE_f']; omega)).symm (hg a le_rfl (by omega)))
    exact (isPerfect_of_distinguished T hT).2.1 h₁ h₃

include hiso hgood in
/-- **`RF(C)` is perfect for a bounded complex `C` whose terms lie in the class.** -/
theorem isPerfect_rightDerivedFunctorPlus_of_bounded (C : CochainComplex A ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b] (hg : ∀ i, good (C.X i)) :
    IsPerfect (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Qh.obj (Functor.plusObj C ⟨a, inferInstance⟩)))) :=
  isPerfect_rightDerivedFunctorPlus_of_bounded_aux F good hiso hgood (b - a).toNat C a _
    (fun i hi => hi.elim (fun hi => C.isZero_of_isStrictlyGE a i hi) (fun hi =>
      C.isZero_of_isStrictlyLE b i (by omega)))
    (fun i _ _ => hg i)

end StacksDraft.Perfect

end
