module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation
import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent

/-!
# The splitting principle in the weak standing situation

The splitting principle for a family of finite locally free modules, stated for
`Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks Section 45.12 in which
the projective bundle formula, condition (4), is only asked to be injective and to resolve the top
power `c₁^A(𝒪_P(1))^{r+1}` of the twist class. The arguments use condition (4) only through these
two properties.

## References

* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-! ### Filtrations with invertible successive quotients -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The splitting principle, Stacks Tag 0FI7.** In the standing situation of Section 45.12, let
`X` be an object of `𝒞` and let `ℰ_i` be a finite collection of locally free `𝒪_X`-modules of
ranks `r_i`. There is a morphism `p : P ⟶ X` of `𝒞` such that `p^* : A(X) ⟶ A(P)` is injective
and each `p^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
`𝒪_P`-modules. The projection is moreover flat.

The induction is on `∑ rᵢ`. If every rank is at most one the identity of `X` already works, each
`ℰ_i` being zero or invertible. Otherwise some `rᵢ` exceeds one; the projective bundle of `ℰ_i`
gives `p : P ⟶ X` with its tautological sequence `0 ⟶ 𝓕 ⟶ p^*ℰ_i ⟶ 𝒪_P(1) ⟶ 0`, and `p^*` is
injective by the projective bundle formula. The inductive hypothesis applied to `𝓕` together
with the `p^*ℰ_{i'}` for `i' ≠ i` produces `q : Q ⟶ P`, and `q ≫ p` is the required morphism:
flatness of `S q` keeps the tautological sequence exact after pullback, so the filtration of
`q^*𝓕` extends by one step to one of `q^*p^*ℰ_i`. -/
theorem exists_injective_hasInvertibleFiltration (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (I : Type*) [Finite I] (E : I → (S.obj X).Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ (P : C) (p : P ⟶ X), Flat (S.map p) ∧ Function.Injective (𝔚.pull p) ∧
      ∀ i, HasInvertibleFiltration (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj (E i)) (r i) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  generalize hn : ∑ i, r i = n
  induction n using Nat.strong_induction_on generalizing X E r with
  | h n ih =>
    by_cases hr : ∀ i, r i ≤ 1
    · refine ⟨X, 𝟙 X, ?_, ?_, fun i => ?_⟩
      · simpa using (inferInstance : Flat (𝟙 (S.obj X)))
      · intro x y h
        simpa [𝔚.pull_id X] using h
      · exact hasInvertibleFiltration_of_rank_le_one _ (r i)
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map (𝟙 X)) (E i) (r i)
            (hE i)) (hr i)
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r i)] using hE i
    set D := 𝔚.bundleDatum X (E i) (r i - 1) hEi with hD
    have hpf : Flat (S.map D.proj) := D.flat
    have hpinj : Function.Injective (𝔚.pull D.proj) := 𝔚.injective_pull_proj X (E i) _ hEi
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j => (Scheme.Modules.pullback (S.map D.proj)).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map D.proj) (E j) (r j)
            (hE j)
    have hlt : ∑ j, Function.update r i (r i - 1) j < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
          omega
        · exact le_of_eq (Function.update_of_ne hj (r i - 1) r)
      · simp only [Function.update_self]
        omega
    obtain ⟨Q, q, hqflat, hqinj, hQ⟩ := ih _ hlt D.bundle _ _ hE' rfl
    have hqf : Flat (S.map q) := hqflat
    refine ⟨Q, q ≫ D.proj, ?_, ?_, fun j => ?_⟩
    · rw [S.map_comp]
      infer_instance
    · simpa only [𝔚.pull_comp q D.proj, RingHom.coe_comp] using hqinj.comp hpinj
    · have comp₁ : (Scheme.Modules.pullback (S.map q)).obj
            ((Scheme.Modules.pullback (S.map D.proj)).obj (E j)) ≅
          (Scheme.Modules.pullback (S.map (q ≫ D.proj))).obj (E j) :=
        (Scheme.Modules.pullbackComp (S.map q) (S.map D.proj)).app (E j) ≪≫
          (Scheme.Modules.pullbackCongr (S.map_comp q D.proj).symm).app (E j)
      by_cases hj : j = i
      · rw [hj] at comp₁ ⊢
        have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
            (Scheme.Modules.pullback (S.map q))).ShortExact :=
          shortExact_map_pullback (S.map q) _ D.shortExact
        have hleft : HasInvertibleFiltration (S.obj Q)
            ((Scheme.Modules.pullback (S.map q)).obj D.sub) (r i - 1) := by
          simpa only [Function.update_self] using hQ i
        have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (S.map q)).obj
              ((Scheme.Modules.pullback (S.map D.proj)).obj (E i))) (r i - 1 + 1) :=
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map q) _ _
            (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map D.proj) (E i) _ hEi)
        have hfil : HasInvertibleFiltration (S.obj Q)
            ((Scheme.Modules.pullback (S.map q)).obj
              ((Scheme.Modules.pullback (S.map D.proj)).obj (E i))) (r i) := by
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r i)] using
            HasInvertibleFiltration.step _ _ _ hDx
              (isInvertible_pullback_obj (S.map q) D.twist D.twist_isInvertible)
              hrank.isFiniteLocallyFree hleft
        exact HasInvertibleFiltration.of_iso comp₁ hfil
      · refine HasInvertibleFiltration.of_iso comp₁ ?_
        simpa only [Function.update_of_ne hj] using hQ j

end ChernSetup

end Stacks.WeilCohomology.Weak

end
