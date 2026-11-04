module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.RankReduction

/-!
# The rank class of a Weil cohomology theory, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankSetup`, stated for
`Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks Section 45.12 in which
the projective bundle formula, condition (4), is only asked to be injective and to resolve the top
power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments use condition (4) only through these two properties.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The reduction of two finite locally free modules to constant rank at once**, by iterating
`Stacks.WeilCohomology.Weak.ChernSetup.exists_clopenRankPieces`: decompose `X` by the rank of `ℰ`,
then each piece by the rank of the restriction of `ℱ`. On a piece of the result both modules have
constant rank, the morphism to `X` is still flat, and a class of `A(X)` is still determined by its
restrictions. -/
theorem ChernSetup.exists_clopenRankPieces_pair (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E F : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    ∃ (ι : Type) (_ : Finite ι) (P : ι → C) (p : ∀ i, P i ⟶ X) (rE rF : ι → ℕ),
      (∀ i, Flat (S.map (p i))) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj E) (rE i)) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj F) (rF i)) ∧
        Function.Injective fun a : 𝔚.A X => fun i => 𝔚.pull (p i) a := by
  classical
  obtain ⟨ι₁, hι₁, P₁, p₁, r₁, hflat₁, hr₁, hinj₁⟩ := 𝔚.exists_clopenRankPieces X E hE
  have : Finite ι₁ := hι₁
  choose ι₂ hι₂ P₂ p₂ r₂ hflat₂ hr₂ hinj₂ using fun i : ι₁ =>
    𝔚.exists_clopenRankPieces (P₁ i) ((Scheme.Modules.pullback (S.map (p₁ i))).obj F)
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map (p₁ i)) F hF)
  have : ∀ i, Finite (ι₂ i) := hι₂
  refine ⟨Σ i, ι₂ i, inferInstance, fun j => P₂ j.1 j.2, fun j => p₂ j.1 j.2 ≫ p₁ j.1,
    fun j => r₁ j.1, fun j => r₂ j.1 j.2, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · have := hflat₁ j.1
    have := hflat₂ j.1 j.2
    rw [S.map_comp]
    infer_instance
  · exact isFiniteLocallyFreeOfRank_pullback_comp (p₂ j.1 j.2) (p₁ j.1) E (r₁ j.1)
      (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map (p₂ j.1 j.2)) _ _
        (hr₁ j.1))
  · exact isFiniteLocallyFreeOfRank_pullback_comp (p₂ j.1 j.2) (p₁ j.1) F (r₂ j.1 j.2)
      (hr₂ j.1 j.2)
  · intro a b hab
    refine hinj₁ (funext fun i => hinj₂ i (funext fun j => ?_))
    have key : ∀ z : 𝔚.A X,
        𝔚.pull (p₂ i j) (𝔚.pull (p₁ i) z) = 𝔚.pull (p₂ i j ≫ p₁ i) z := by
      intro z
      rw [𝔚.pull_comp]
      rfl
    have h := congrFun hab ⟨i, j⟩
    dsimp only at h ⊢
    rw [key a, key b]
    exact h

namespace ChernSetup

variable (𝔚 : ChernSetup.{u, v, v₁, w} C S)

/-- **The rank class exists.** There is a class of `A(X)` which restricts to `r` along every
morphism of `𝒞` along which `ℰ` acquires constant rank `r`, and which is `0` when `ℰ` is not
finite locally free.

For a finite locally free `ℰ` this is the patching half of condition (2),
`Stacks.WeilCohomology.Weak.ChernSetup.exists_pull_eq_constantRank`, applied to the datum that
assigns the natural number `m` to a morphism making the rank `m`: that datum is compatible with
further pullback because `f^*` is a ring map and so preserves natural numbers. -/
theorem exists_rankClass (X : C) (E : (S.obj X).Modules) :
    ∃ a : 𝔚.A X,
      (∀ (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (Z : C)
          (g : Z ⟶ X) (m : ℕ),
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔚.pull g a = (m : 𝔚.A Z)) ∧
        (¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E → a = 0) := by
  by_cases hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E
  · obtain ⟨a, ha⟩ := 𝔚.exists_pull_eq_constantRank X E hE (fun Z _ m _ => (m : 𝔚.A Z))
      fun _ _ _ h m _ _ => map_natCast (𝔚.pull h) m
    exact ⟨a, fun _ Z g m hm => ha Z g m hm, fun hnot =>
      absurd ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr hE)
        hnot⟩
  · exact ⟨0, fun hE' => absurd hE' hE, fun _ => rfl⟩

/-- **The rank class `r^A(ℰ)`**, extended by zero off the finite locally free modules: the class
of `A^0(X)` which restricts to the constant rank of `ℰ` wherever `ℰ` acquires one. -/
def rankClass (X : C) (E : (S.obj X).Modules) : 𝔚.A X := (𝔚.exists_rankClass X E).choose

/-- **The defining property of the rank class**: wherever a finite locally free module acquires
constant rank `r`, its rank class restricts to `r`. -/
theorem rankClass_pull_eq {X Y : C} (g : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) r) :
    𝔚.pull g (𝔚.rankClass Y E) = (r : 𝔚.A X) :=
  (𝔚.exists_rankClass Y E).choose_spec.1 hE X g r hr

/-- The rank class vanishes off the finite locally free modules, which is the normalisation the
universal property of the Grothendieck ring asks for. -/
theorem rankClass_eq_zero (X : C) (M : (S.obj X).Modules)
    (h : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M) : 𝔚.rankClass X M = 0 :=
  (𝔚.exists_rankClass X M).choose_spec.2 h

/-- **The rank class of a module of constant rank `r` is `r`.** This is the defining property at
the identity morphism. -/
theorem rankClass_eq (X : C) (M : (S.obj X).Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    𝔚.rankClass X M = (r : 𝔚.A X) := by
  have h' := 𝔚.rankClass_pull_eq (𝟙 X) M h.isFiniteLocallyFree r
    (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map (𝟙 X)) M r h)
  rwa [𝔚.pull_id X, RingHom.id_apply] at h'

/-- **The rank class lies in `A^0(X)`.** Its restriction to every piece on which the rank is
constant is a natural number, which lies in degree zero, and condition (2) is a splitting of
graded rings. -/
theorem rankClass_mem_grade (X : C) (M : (S.obj X).Modules) :
    𝔚.rankClass X M ∈ 𝔚.grade X 0 := by
  by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M
  · refine 𝔚.mem_grade_of_pull_constantRank X M hM _ 0 fun Z g _ m hm => ?_
    rw [𝔚.rankClass_pull_eq g M hM m hm]
    exact 𝔚.natCast_mem_grade_zero Z m
  · rw [𝔚.rankClass_eq_zero X M fun h =>
      hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h)]
    exact (𝔚.grade X 0).zero_mem

/-- **The rank class is compatible with pullback.** Restricting to the pieces on which the
pulled-back module has constant rank, which is
`Stacks.WeilCohomology.Weak.ChernSetup.exists_clopenRankPieces`, both sides become that constant
rank, and a class is determined by those restrictions. -/
theorem pull_rankClass {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    𝔚.pull f (𝔚.rankClass Y E) = 𝔚.rankClass X ((Scheme.Modules.pullback (S.map f)).obj E) := by
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E hE
  obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ :=
    𝔚.exists_clopenRankPieces X ((Scheme.Modules.pullback (S.map f)).obj E) hE'
  refine hinj (funext fun i => ?_)
  dsimp only
  rw [← RingHom.comp_apply, ← 𝔚.pull_comp (p i) f,
    𝔚.rankClass_pull_eq (p i ≫ f) E hE (r i)
      (isFiniteLocallyFreeOfRank_pullback_comp (p i) f E (r i) (hr i)),
    𝔚.rankClass_pull_eq (p i) _ hE' (r i) (hr i)]

end ChernSetup

end Stacks.WeilCohomology.Weak

end
