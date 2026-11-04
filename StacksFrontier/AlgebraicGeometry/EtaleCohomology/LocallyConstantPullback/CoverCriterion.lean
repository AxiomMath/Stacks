module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.OverMapConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Local constancy is checked on one covering of the final object

Let `J` be a Grothendieck topology on a category `C` with pullbacks and a final object `T`. By
definition a locally constant sheaf becomes constant on a covering of *every* object of `C`, and
nothing in the definition says that one trivialization is enough: trivializing over a second
object refines the covering, and a priori the first trivialization need not survive the
refinement.

It does survive it. `Stacks.ConstantSheaf.overPullbackIsoOfMap` says that a trivialization over
`Y`, with value `A`, restricts along an arbitrary morphism `X ⟶ Y` of the site to a
trivialization over `X` with the same value `A`. Pulling a covering of the final object back to an
arbitrary object `U` therefore produces a covering of `U` by objects over which the sheaf is
already trivialized, with the same values. So a single covering of the final object suffices, and
the same holds for finite local constancy because the values are unchanged.

This is the form in which local constancy is used throughout the constructibility chain of
Chapter 59: there the site is the small étale site of a scheme `X`, whose final object is `X`
itself, and every covering produced by geometry is a covering of `X`.

## Main results

* `Stacks.ConstantSheaf.isConstant_over_of_cover` — a sheaf which is constant over each member of
  a covering of the final object is constant over every object admitting a morphism into a member.
* `Stacks.ConstantSheaf.isLocallyConstant_of_isConstant_cover` and
  `Stacks.ConstantSheaf.isLocallyConstant_iff_isConstant_cover` — local constancy from, and
  equivalent to, one covering of the final object.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_finite_cover` and
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_finite_cover` — the same for finite local
  constancy, where the constant values are carried along unchanged.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]
  [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

omit [HasPullbacks C] [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- The family of all arrows of a covering sieve is a covering family. -/
public lemma sieve_ofArrows_arrows_mem {U : C} (R : Sieve U) (hR : R ∈ J U) :
    Sieve.ofArrows (fun p : Σ V : C, {g : V ⟶ U // R.arrows g} => p.1)
      (fun p => p.2.1) ∈ J U := by
  convert hR using 1
  refine le_antisymm ?_ ?_
  · intro V g hg
    obtain ⟨p, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact R.downward_closed p.2.2 h
  · intro V g hg
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨⟨V, g, hg⟩, 𝟙 _, by simp⟩

/-- A covering of the final object pulls back to a covering of any `U` whose members each map to
some member of the original covering. -/
private theorem exists_cover_over_of_cover {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T) {I : Type*} {X : I → C}
    {f : ∀ i, X i ⟶ T} (hf : Sieve.ofArrows X f ∈ J T) (U : C) :
    ∃ (ι : Type (max u v)) (Y : ι → C) (g : ∀ j, Y j ⟶ U), Sieve.ofArrows Y g ∈ J U ∧
      ∀ j, ∃ i, Nonempty (Y j ⟶ X i) := by
  refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
    fun p => p.1, fun p => p.2.1,
    sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp p.2.2
  exact ⟨i, ⟨h⟩⟩

/-- A sheaf trivialized on a covering `{X i ⟶ T}` of the final object is trivialized over every
object `V` of the site: the covering pulls back to a covering of `V`, and each of its members
maps to some `X i`, over which the sheaf is already constant. -/
public lemma isConstant_over_of_cover {T : C} (hT : IsTerminal T) (F : Sheaf J (Type w))
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hc : ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback (Type w) (X i)).obj F))
    {V : C} (hV : (Sieve.ofArrows X f).arrows (hT.from V)) :
    Sheaf.IsConstant (J.over V) ((J.overPullback (Type w) V).obj F) := by
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hV
  have := hc i
  exact isConstant_over_of_isConstant_over J h F

/-- **A single covering of the final object suffices for local constancy.** If a sheaf of sets
becomes constant after restriction to each member of one covering of the final object of the site,
then it is locally constant. -/
public lemma isLocallyConstant_of_isConstant_cover {T : C} (hT : IsTerminal T)
    (F : Sheaf J (Type w)) {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback (Type w) (X i)).obj F)) :
    IsLocallyConstant J F where
  exists_cover U := by
    obtain ⟨ι, Y, g, hg, hY⟩ := exists_cover_over_of_cover J hT hf U
    refine ⟨ι, Y, g, hg, fun j => ?_⟩
    obtain ⟨i, ⟨h⟩⟩ := hY j
    have := hc i
    exact isConstant_over_of_isConstant_over J h F

/-- **Local constancy is equivalent to trivializability on one covering of the final object.** -/
public lemma isLocallyConstant_iff_isConstant_cover {T : C} (hT : IsTerminal T)
    (F : Sheaf J (Type w)) :
    IsLocallyConstant J F ↔
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ T), Sieve.ofArrows X f ∈ J T ∧
        ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback (Type w) (X i)).obj F) :=
  ⟨fun h => h.exists_cover T, fun ⟨_, _, _, hf, hc⟩ =>
    isLocallyConstant_of_isConstant_cover J hT F hf hc⟩

/-- **A single covering of the final object suffices for finite local constancy.** The constant
values produced by the hypothesis are the constant values produced by the conclusion, so any
property of them — finiteness here — is preserved. -/
public lemma isFiniteLocallyConstant_of_finite_cover {T : C} (hT : IsTerminal T)
    (F : Sheaf J (Type w)) {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ A : Type w, Finite A ∧ Nonempty
      ((constantSheaf (J.over (X i)) (Type w)).obj A ≅ (J.overPullback (Type w) (X i)).obj F)) :
    IsFiniteLocallyConstant (FD := TypeCat.Fun) (CD := fun A : Type w => A) J F where
  exists_finite_cover U := by
    obtain ⟨ι, Y, g, hg, hY⟩ := exists_cover_over_of_cover J hT hf U
    refine ⟨ι, Y, g, hg, fun j => ?_⟩
    obtain ⟨i, ⟨h⟩⟩ := hY j
    obtain ⟨A, hA, ⟨e⟩⟩ := hc i
    exact ⟨A, hA, ⟨overPullbackIsoOfMap J h F A e⟩⟩

/-- **Finite local constancy is equivalent to finite trivializability on one covering of the final
object.** -/
public lemma isFiniteLocallyConstant_iff_finite_cover {T : C} (hT : IsTerminal T)
    (F : Sheaf J (Type w)) :
    IsFiniteLocallyConstant (FD := TypeCat.Fun) (CD := fun A : Type w => A) J F ↔
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ T), Sieve.ofArrows X f ∈ J T ∧
        ∀ i, ∃ A : Type w, Finite A ∧ Nonempty
          ((constantSheaf (J.over (X i)) (Type w)).obj A ≅
            (J.overPullback (Type w) (X i)).obj F) :=
  ⟨fun h => h.exists_finite_cover T, fun ⟨_, _, _, hf, hc⟩ =>
    isFiniteLocallyConstant_of_finite_cover J hT F hf hc⟩

end Stacks.ConstantSheaf

end
