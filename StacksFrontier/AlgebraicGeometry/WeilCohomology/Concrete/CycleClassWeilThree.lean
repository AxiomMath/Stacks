module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseGeneral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsAxiom
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree

/-!
# Axioms (C)(a), (C)(c) and the condition of Lemma 0FI0 for data satisfying (A1)–(A8)

Let (D0), (D1), (D2') satisfy axioms (A1)–(A6), and let `toWeilData` be the data of Section 0FHA
they define: the cycle class map `γ` of Tag 0FIF read in `H^{2i}(X)(i)`, and the trace map `λ`
of axiom (A6). Then:

* axiom (C)(a) holds, `γ(f^!β) = f^*γ(β)`, since `γ` commutes with the Gysin maps of Tag 0FF3;
* axiom (C)(c) holds, `γ(α · β) = γ(α) ∪ γ(β)`, since `γ` is multiplicative;
* under axiom (A8), the condition of Definition 0FI2 holds (condition (2) of Lemma 0FI0 for every
  `X`), which is axiom (A8) itself.

These are the parts of the proof of Proposition 0FIU attributed to the construction of `γ`. In
negative codimension the Chow groups vanish (`subsingleton_codimensionChowGroup_of_neg`), where
`γ` is zero.

## Main results

* `Stacks.Chow.subsingleton_codimensionChowGroup_of_neg`: `CH^i(X) = 0` for `i < 0`.
* `IsCohomologicalChernCharacter.cycleClassPullback_toWeilData`: axiom (C)(a).
* `IsCohomologicalChernCharacter.cycleClassMul_toWeilData`: axiom (C)(c).
* `IsCohomologicalChernCharacter.globalSectionsCondition_toWeilData`: (A8) gives the condition of
  Lemma 0FI0 required by Definition 0FI2.

## References

* [Stacks Project, Tag 0FIU](https://stacks.math.columbia.edu/tag/0FIU)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.Chow

/-- **The Chow groups vanish in negative codimension**: for `X` smooth over `k` and `i < 0`,
`CH^i(X) = ∏_d CH_{d-i}(X_d)` is zero, the part `X_d` having dimension at most `d < d - i`. -/
theorem subsingleton_codimensionChowGroup_of_neg (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [Smooth sX] {i : ℤ}
    (hi : i < 0) : Subsingleton (codimensionChowGroup k sX i) := by
  refine ⟨fun a b ↦ funext fun d ↦ ?_⟩
  exact (subsingleton_chowGroup_of_schemeDeltaDimension_le (fieldChowSituation k)
    (Stacks.WeilCohomology.partBase sX d) (schemeDeltaDimension_partBase_le sX d)
    (by omega : (d : ℤ) < d - i)).elim _ _

end Stacks.Chow

namespace Stacks.WeilCohomology.FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

/-- Reading `H^n(X)(m)` inside `H^*(X)(m)` is injective. -/
theorem tateTwistMap_subtype_injective (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    Function.Injective (tateTwistMap (L := 𝔇.tate) (𝔇.grade X n).subtype m) := by
  intro x y hxy
  apply (tateTwistCoordinates 𝔇.coord m).injective
  apply Subtype.val_injective
  have := congrArg (tateTwistCoordinates 𝔇.coord m) hxy
  rwa [tateTwistCoordinates_map, tateTwistCoordinates_map] at this

end Stacks.WeilCohomology.FirstChernClassData

namespace Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom)
  (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)

/-- Pullback on `H^m(-)(n)` of `toWeilData`, read inside `H^*(-)(n)`, is the pullback of `𝔇`. -/
theorem tateTwistMap_subtype_pullTw_toWeilData
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (m n : ℤ)
    (x : tateTwist F 𝔇.tate (𝔇.grade Y m) n) :
    tateTwistMap (𝔇.grade X m).subtype n ((h.toWeilData hA1 hA3 hA5 hA6).pullTw f m n x) =
      𝔇.pullTw f n (tateTwistMap (𝔇.grade Y m).subtype n x) := by
  have key : (tateTwistMap (𝔇.grade X m).subtype n).comp
      ((h.toWeilData hA1 hA3 hA5 hA6).pullTw f m n) =
        (𝔇.pullTw f n).comp (tateTwistMap (𝔇.grade Y m).subtype n) :=
    TensorProduct.ext' fun _ _ ↦ rfl
  exact LinearMap.congr_fun key x

/-- The twisted cup product of `toWeilData`, read inside `H^*(X)(m)`, is the twisted cup product
of `𝔇`. -/
theorem tateTwistMap_subtype_cupTw_toWeilData (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i j p : ℤ) (hij : i + j = p) (s t m : ℤ) (hst : s + t = m)
    (a : tateTwist F 𝔇.tate (𝔇.grade X i) s) (b : tateTwist F 𝔇.tate (𝔇.grade X j) t) :
    tateTwistMap (𝔇.grade X p).subtype m
        ((h.toWeilData hA1 hA3 hA5 hA6).cupTw X i j p hij s t m hst a b) =
      tateCup 𝔇.finrank_tate (𝔇.cup X) s t m hst (tateTwistMap (𝔇.grade X i).subtype s a)
        (tateTwistMap (𝔇.grade X j).subtype t b) := by
  apply (tateTwistCoordinates 𝔇.coord m).injective
  refine (tateTwistCoordinates_map 𝔇.coord m (𝔇.grade X p).subtype _).trans ?_
  refine (congrArg Subtype.val (tateTwistCoordinates_tateCup 𝔇.finrank_tate
    ((h.toWeilData hA1 hA3 hA5 hA6).cup X i j p hij) s t m hst a b)).trans ?_
  refine Eq.trans ?_ (tateTwistCoordinates_tateCup 𝔇.finrank_tate (𝔇.cup X) s t m hst _ _).symm
  refine (congrArg₂ (fun u v ↦ u * v)
    (tateTwistCoordinates_map 𝔇.coord s (𝔇.grade X i).subtype a)
    (tateTwistCoordinates_map 𝔇.coord t (𝔇.grade X j).subtype b)).symm.trans ?_
  rfl

/-- **Axiom (C)(a)** for the data of (A1)–(A6): `γ(f^!β) = f^*γ(β)` for a morphism `f : X ⟶ Y`
of smooth projective schemes over `k` and `β ∈ CH^i(Y)`, `f^!` the Gysin map of Tag 0FF3. -/
theorem cycleClassPullback_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).CycleClassPullback := by
  intro X Y f i β
  match i with
  | Int.ofNat n =>
    refine tateTwistMap_subtype_injective (𝔇 := 𝔇) X _ _ ?_
    exact (h.tateTwistMap_toWeilData_cycleClass hA1 hA3 hA5 hA6 X n _).trans
      ((h.codimensionCycleClass_codimensionGysin f n β).trans
        ((congrArg (𝔇.pullTw f n)
          (h.tateTwistMap_toWeilData_cycleClass hA1 hA3 hA5 hA6 Y n β).symm).trans
          (h.tateTwistMap_subtype_pullTw_toWeilData hA1 hA3 hA5 hA6 f _ _ _).symm))
  | Int.negSucc n =>
    change (0 : _ →+ _) _ = (h.toWeilData hA1 hA3 hA5 hA6).pullTw f _ _ ((0 : _ →+ _) β)
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]

/-- **Axiom (C)(c)** for the data of (A1)–(A6): `γ(α · β) = γ(α) ∪ γ(β)` for `α ∈ CH^i(X)`,
`β ∈ CH^j(X)` and the intersection product of Stacks 0FC0. In negative codimension both sides
vanish, the Chow groups being zero there. -/
theorem cycleClassMul_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).CycleClassMul := by
  intro X i j α β
  match i, j with
  | Int.ofNat n, Int.ofNat m =>
    refine tateTwistMap_subtype_injective (𝔇 := 𝔇) X _ _ ?_
    have L := h.tateTwistMap_toWeilData_cycleClass hA1 hA3 hA5 hA6 X
    refine (L (n + m) _).trans ?_
    refine (h.codimensionCycleClass_codimensionIntersectionProduct hA1 hA3 X n m α β).trans ?_
    refine Eq.trans ?_
      (h.tateTwistMap_subtype_cupTw_toWeilData hA1 hA3 hA5 hA6 X _ _ _ _ _ _ _ _ _ _).symm
    exact congrArg₂ _ (congrArg _ (L n α).symm) (L m β).symm
  | Int.negSucc n, j =>
    obtain rfl :=
      (subsingleton_codimensionChowGroup_of_neg k X.obj.hom (Int.negSucc_lt_zero n)).elim α 0
    simp only [map_zero, LinearMap.zero_apply]
  | Int.ofNat n, Int.negSucc m =>
    obtain rfl :=
      (subsingleton_codimensionChowGroup_of_neg k X.obj.hom (Int.negSucc_lt_zero m)).elim β 0
    simp only [map_zero]

/-- **The condition of Definition 0FI2 is axiom (A8)**: under (A8), condition (2) of Lemma 0FI0
holds for the data `toWeilData` and every smooth projective `X`, i.e.
`H^0(Spec Γ(X, 𝒪_X)) ⟶ H^0(X)` is an isomorphism. -/
theorem globalSectionsCondition_toWeilData (hA8 : 𝔇.GlobalSectionsAxiom) :
    (h.toWeilData hA1 hA3 hA5 hA6).GlobalSectionsCondition :=
  hA8

end Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

end
