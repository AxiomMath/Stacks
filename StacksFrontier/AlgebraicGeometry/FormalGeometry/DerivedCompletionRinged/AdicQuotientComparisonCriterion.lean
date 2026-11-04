module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization

/-!
# A criterion for the failure of the comparison map of Tag 0CQH

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `K ↦ K^∧` a derived completion
functor and `K ∈ D(𝒪)`. `AdicQuotientFactorization.lean` builds the comparison map

`K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`

of [Stacks, Tag 0CQH]. This file gives a criterion under which no such map is invertible, in the
form a witness can supply: a non-zero compatible family of classes on the reduction tower from
an object that sees nothing of `K^∧`, and the recipe that produces such classes from two towers
of distinguished triangles.

## Main results

* `Stacks.InverseSystem.not_isIso_of_cone_of_forall_hom_eq_zero`: if `Y` admits no non-zero map
  into `W` but a non-zero cone over a tower, no map `W ⟶ L` into a derived limit of the tower is
  invertible.
* `Stacks.InverseSystem.exists_cone_shift_of_triangleTower`: along a tower of distinguished
  triangles `Aₙ ⟶ B ⟶ Tₙ ⟶ Aₙ[1]` with constant middle term `B` and no non-zero map
  `Y[1] ⟶ B`, a non-zero cone `Y ⟶ Aₙ` dying in `B` lifts to a non-zero cone `Y[1] ⟶ Tₙ`.
* `AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_of_periodicPresentation`:
  at a derived-complete sheaf `M` and two towers of triangles presenting the reductions
  two-periodically, one non-zero compatible family of degree-`0` classes dying in `M` defeats every
  comparison map.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped IsMulCommutative

namespace Stacks.InverseSystem

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A non-zero cone from an object orthogonal to the source obstructs invertibility of a map
into a derived limit.** If no map `Y ⟶ W` is non-zero, while the maps `uₙ : Y ⟶ Tₙ` form a cone
over the tower with some `u_m ≠ 0`, then a map `c : W ⟶ L` into a derived limit of the tower is
not invertible.

The cone kills the Milnor difference, so it factors as `u = g ≫ p` through the base of the
Milnor triangle. Were `c` invertible, `g` would be `(g ≫ c⁻¹) ≫ c`, and `g ≫ c⁻¹ : Y ⟶ W` is
zero by hypothesis; then `u_m = g ≫ p ≫ π_m` would be zero. No compatibility between `c` and
the cone is used, so the conclusion holds for every map `W ⟶ L` whatsoever. -/
theorem not_isIso_of_cone_of_forall_hom_eq_zero (T : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => T.obj ⟨n⟩] {Y W L : D}
    (hY : ∀ g : Y ⟶ W, g = 0)
    (u : ∀ n : ℕ, Y ⟶ T.obj ⟨n⟩)
    (hu : ∀ n : ℕ, u (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = u n)
    {m : ℕ} (hm : u m ≠ 0)
    {p : L ⟶ ∏ᶜ fun n : ℕ => T.obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => T.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => T.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang D)
    (c : W ⟶ L) : ¬ IsIso c := by
  intro hc
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ htri (Pi.lift u) <|
    Pi.hom_ext _ _ fun n => by
      rw [Category.assoc]
      simp [hu n]
  have hg' : Pi.lift u = g ≫ p := hg
  have hg0 : g = 0 := (Preadditive.IsIso.comp_right_eq_zero g (inv c)).1 (hY _)
  refine hm ?_
  rw [← Pi.lift_π u m, hg', hg0, zero_comp, zero_comp]

/-- **Raising the degree of a cone along a tower of distinguished triangles with constant
middle term.** Suppose each `Aₙ --αₙ--> B --βₙ--> Tₙ --γₙ--> Aₙ[1]` is distinguished, the `γₙ`
commute with the transition maps of the two towers, and no map `Y[1] ⟶ B` is non-zero. Then a
non-zero cone `(wₙ : Y ⟶ Aₙ)` over the tower `A` produces a non-zero cone
`(uₙ : Y[1] ⟶ Tₙ)` over the tower `T`, provided each `wₙ` dies in `B`.

Composition with `γₙ` is injective on `Hom(Y[1], Tₙ)` because the previous term of the
long exact sequence is `Hom(Y[1], B) = 0`, and it hits `wₙ[1]` because `wₙ ≫ αₙ = 0`. The
lift is therefore unique, so the lifts inherit the compatibility of the `wₙ` and the
non-vanishing of `w_m`.

This is the step by which a witness for the last clause of [Stacks, Tag 0CQH] is assembled.
For `ℐ = (a)` principal, the short exact sequences `0 → 𝒪a → 𝒪 → 𝒪/ℐ → 0` and
`0 → ker(a) → 𝒪 → 𝒪a → 0` tensor up to two such towers of triangles with `B = K`, and two
applications carry a degree `0` class — the reduction map itself — to a degree `-2` class.
That is the degree in which the classes survive the limit when `a` is a zero-divisor whose
annihilator is again `𝒪/ℐ`, the two-periodic case. -/
theorem exists_cone_shift_of_triangleTower {Y B : D} (T A : ℕᵒᵖ ⥤ D)
    (α : ∀ n : ℕ, A.obj ⟨n⟩ ⟶ B) (β : ∀ n : ℕ, B ⟶ T.obj ⟨n⟩)
    (γ : ∀ n : ℕ, T.obj ⟨n⟩ ⟶ (A.obj ⟨n⟩)⟦(1 : ℤ)⟧)
    (htri : ∀ n : ℕ, Triangle.mk (α n) (β n) (γ n) ∈ distTriang D)
    (hγ : ∀ n : ℕ, T.map (homOfLE (Nat.le_succ n)).op ≫ γ n =
      γ (n + 1) ≫ (shiftFunctor D (1 : ℤ)).map (A.map (homOfLE (Nat.le_succ n)).op))
    (hB : ∀ g : (shiftFunctor D (1 : ℤ)).obj Y ⟶ B, g = 0)
    (w : ∀ n : ℕ, Y ⟶ A.obj ⟨n⟩)
    (hwα : ∀ n : ℕ, w n ≫ α n = 0)
    (hw : ∀ n : ℕ, w (n + 1) ≫ A.map (homOfLE (Nat.le_succ n)).op = w n)
    {m : ℕ} (hm : w m ≠ 0) :
    ∃ u : ∀ n : ℕ, (shiftFunctor D (1 : ℤ)).obj Y ⟶ T.obj ⟨n⟩,
      (∀ n : ℕ, u (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = u n) ∧ u m ≠ 0 := by
  have hinj : ∀ (n : ℕ) (v : (shiftFunctor D (1 : ℤ)).obj Y ⟶ T.obj ⟨n⟩),
      v ≫ γ n = 0 → v = 0 := by
    intro n v hv
    obtain ⟨ψ, hψ⟩ := (Triangle.mk (α n) (β n) (γ n)).coyoneda_exact₃ (htri n) v hv
    rw [hψ, hB ψ, zero_comp]
  have hex : ∀ n : ℕ, ∃ v : (shiftFunctor D (1 : ℤ)).obj Y ⟶ T.obj ⟨n⟩,
      (shiftFunctor D (1 : ℤ)).map (w n) = v ≫ γ n := by
    intro n
    refine (Triangle.mk (α n) (β n) (γ n)).rotate.coyoneda_exact₃
      (rot_of_distTriang _ (htri n)) ((shiftFunctor D (1 : ℤ)).map (w n)) ?_
    show (shiftFunctor D (1 : ℤ)).map (w n) ≫ (-(shiftFunctor D (1 : ℤ)).map (α n)) = 0
    rw [Preadditive.comp_neg, ← Functor.map_comp, hwα n, Functor.map_zero, neg_zero]
  choose u hu using hex
  refine ⟨u, fun n => ?_, ?_⟩
  · have h1 : (u (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op - u n) ≫ γ n = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hγ n, ← Category.assoc, ← hu (n + 1),
        ← Functor.map_comp, hw n, ← hu n, sub_self]
    exact sub_eq_zero.1 (hinj n _ h1)
  · intro h0
    refine hm ((shiftFunctor D (1 : ℤ)).map_injective ?_)
    rw [Functor.map_zero, hu m, h0, zero_comp]

end Stacks.InverseSystem

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Single

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The shift of a single complex by `j` is concentrated in degrees `≤ -j`. -/
theorem isLE_shift_single (N : C) (j : ℤ) :
    (((DerivedCategory.singleFunctor C 0).obj N)⟦j⟧).IsLE (-j) :=
  DerivedCategory.TStructure.t.isLE_shift _ 0 j (-j) (by omega)

/-- A complex concentrated in degrees `≤ j` is concentrated in degrees `≤ j - 1` after a shift
by one. -/
theorem isLE_shift_one (Y : DerivedCategory C) (j : ℤ) [Y.IsLE j] :
    (Y⟦(1 : ℤ)⟧).IsLE (j - 1) :=
  DerivedCategory.TStructure.t.isLE_shift _ j 1 (j - 1) (by omega)

/-- **A positively shifted single complex admits no non-zero map into a single complex.** -/
theorem hom_shift_single_single_eq_zero (N M : C) {j : ℤ} (hj : 0 < j)
    (g : ((DerivedCategory.singleFunctor C 0).obj N)⟦j⟧ ⟶
      (DerivedCategory.singleFunctor C 0).obj M) : g = 0 :=
  have := isLE_shift_single N j
  DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g (-j) 0 (by omega) inferInstance inferInstance

end Single

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- Countable products exist in `D(𝒪)`, as
`AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf` at a single
universe. -/
local instance hasProductsOfShape_nat_derivedCategory_ringSheaf_adicQuotientComparison :
    HasProductsOfShape ℕ
        (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

/-- **The criterion at the reduction tower.** If an object `Y` admits no non-zero map into the
derived completion `K^∧`, while it does admit a non-zero cone over the reduction tower
`n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, then no map `K^∧ ⟶ L` into a derived limit of that tower is
invertible. -/
theorem not_isIso_derivedCompletionComparison_of_cone
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hY : ∀ g : Y ⟶ (derivedCompletion X I).obj K, g = 0)
    (u : ∀ n : ℕ, Y ⟶ (adicReductionTower X I K).obj ⟨n⟩)
    (hu : ∀ n : ℕ,
      u (n + 1) ≫ (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op = u n)
    {m : ℕ} (hm : u m ≠ 0)
    {L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) (n + 1) ≫
            (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (c : (derivedCompletion X I).obj K ⟶ L) : ¬ IsIso c :=
  Stacks.InverseSystem.not_isIso_of_cone_of_forall_hom_eq_zero _ hY u hu hm htri c

/-- **A complex concentrated in negative degrees admits no non-zero map into the derived
completion of a derived-complete single complex.** The completion unit is invertible on a
derived-complete object, so the target is isomorphic to a single complex. -/
theorem hom_isLE_derivedCompletion_single_eq_zero
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : IsDerivedComplete.{u, u, u, u} X I
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M))
    {Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {j : ℤ} (hj : j < 0) [Y.IsLE j]
    (g : Y ⟶ (derivedCompletion X I).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)) :
    g = 0 := by
  have := isIso_derivedCompletionUnit_app X I hM
  exact (Preadditive.IsIso.comp_right_eq_zero g (inv ((derivedCompletionUnit X I).app _))).1
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
      (Y := (DerivedCategory.singleFunctor _ 0).obj M) _ j 0 hj inferInstance inferInstance)

section SingleReduction

variable (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (hM : IsDerivedComplete.{u, u, u, u} X I
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M))

include hM

/-- **The criterion at a derived-complete sheaf.** For a sheaf of modules `M` whose single
complex is derived complete, a non-zero compatible family of maps from a complex concentrated in
negative degrees into the reductions `M ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` defeats every comparison map. -/
theorem not_isIso_derivedCompletionComparison_of_singleCone
    {Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {j : ℤ} (hj : j < 0) [Y.IsLE j]
    (u : ∀ n : ℕ, Y ⟶
        (adicReductionTower X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩)
    (hu : ∀ n : ℕ, u (n + 1) ≫ (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
          (homOfLE (Nat.le_succ n)).op = u n)
    {m : ℕ} (hm : u m ≠ 0)
    {L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => (adicReductionTower X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (adicReductionTower X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩)
            n -
          Pi.π (fun n : ℕ => (adicReductionTower X I
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj
              ⟨n⟩) (n + 1) ≫
            (adicReductionTower X I
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (c : (derivedCompletion X I).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M) ⟶ L) :
    ¬ IsIso c :=
  not_isIso_derivedCompletionComparison_of_cone X I _
    (hom_isLE_derivedCompletion_single_eq_zero X I M hM hj) u hu hm htri c

/-- **The criterion at a two-periodic presentation of the reductions.** Let `M` be a sheaf of
modules whose single complex `M[0]` is derived complete, and suppose the reductions
`Tₙ = M[0] ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` sit in two towers of distinguished triangles

`Jₙ ⟶ M[0] ⟶ Tₙ ⟶ Jₙ[1]` and `Tₙ ⟶ M[0] ⟶ Jₙ ⟶ Tₙ[1]`

whose connecting maps commute with the transition maps. Then a single non-zero compatible
family `vₙ : N[0] ⟶ Tₙ` of degree-`0` classes dying in `M[0]` under the second tower defeats
every comparison map. Two applications of
`Stacks.InverseSystem.exists_cone_shift_of_triangleTower` carry `v` into degree `-2`, where
`not_isIso_derivedCompletionComparison_of_singleCone` applies. -/
theorem not_isIso_derivedCompletionComparison_of_periodicPresentation
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (J : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (α₂ : ∀ n : ℕ, (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩ ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)
    (β₂ : ∀ n : ℕ, (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M ⟶
      J.obj ⟨n⟩)
    (γ₂ : ∀ n : ℕ, J.obj ⟨n⟩ ⟶ ((adicReductionTower X I
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj
        ⟨n⟩)⟦(1 : ℤ)⟧)
    (htri₂ : ∀ n : ℕ, Triangle.mk (α₂ n) (β₂ n) (γ₂ n) ∈
      distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (hγ₂ : ∀ n : ℕ, J.map (homOfLE (Nat.le_succ n)).op ≫ γ₂ n =
      γ₂ (n + 1) ≫ (shiftFunctor
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (1 : ℤ)).map ((adicReductionTower X I
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
            (homOfLE (Nat.le_succ n)).op))
    (α₁ : ∀ n : ℕ, J.obj ⟨n⟩ ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)
    (β₁ : ∀ n : ℕ, (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M ⟶
      (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩)
    (γ₁ : ∀ n : ℕ, (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩ ⟶
      (J.obj ⟨n⟩)⟦(1 : ℤ)⟧)
    (htri₁ : ∀ n : ℕ, Triangle.mk (α₁ n) (β₁ n) (γ₁ n) ∈
      distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (hγ₁ : ∀ n : ℕ, (adicReductionTower X I
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
            (homOfLE (Nat.le_succ n)).op ≫ γ₁ n =
      γ₁ (n + 1) ≫ (shiftFunctor
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (1 : ℤ)).map (J.map (homOfLE (Nat.le_succ n)).op))
    (v : ∀ n : ℕ, (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj N ⟶
      (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩)
    (hvα : ∀ n : ℕ, v n ≫ α₂ n = 0)
    (hv : ∀ n : ℕ, v (n + 1) ≫ (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
          (homOfLE (Nat.le_succ n)).op = v n)
    {m : ℕ} (hm : v m ≠ 0)
    {L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    {p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩}
    {δ : (∏ᶜ fun n : ℕ => (adicReductionTower X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧}
    (htri : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (adicReductionTower X I
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj ⟨n⟩)
            n -
          Pi.π (fun n : ℕ => (adicReductionTower X I
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).obj
              ⟨n⟩) (n + 1) ≫
            (adicReductionTower X I
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang
          (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
    (c : (derivedCompletion X I).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M) ⟶ L) :
    ¬ IsIso c := by
  obtain ⟨u, hu, hum⟩ :=
    Stacks.InverseSystem.exists_cone_shift_of_triangleTower J
      (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M))
      α₂ β₂ γ₂ htri₂ hγ₂
      (fun g => hom_shift_single_single_eq_zero N M (j := 1) (by norm_num) g) v hvα hv hm
  have := isLE_shift_single N (1 : ℤ)
  have := isLE_shift_one (((DerivedCategory.singleFunctor _ 0).obj N)⟦(1 : ℤ)⟧) (-1)
  obtain ⟨u', hu', hum'⟩ :=
    Stacks.InverseSystem.exists_cone_shift_of_triangleTower
      (adicReductionTower X I
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M))
      J α₁ β₁ γ₁ htri₁ hγ₁
      (fun g => DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g (-1 - 1) 0 (by norm_num)
        inferInstance inferInstance) u
      (fun n => DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-1) 0 (by norm_num)
        inferInstance inferInstance) hu hum
  exact not_isIso_derivedCompletionComparison_of_singleCone X I M hM (j := -1 - 1)
    (by norm_num) u' hu' hum' htri c

end SingleReduction

end AlgebraicGeometry.RingedSite

end
